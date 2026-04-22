"""
InteractiveSessionManager: REPL wrapper around ProofController for collaborative
human-agent proof development.

Commands:
  step              — agent takes one tactic/rollback action
  run               — agent runs until subgoal changes, failure, or proof complete
  tactic <tac>      — apply user-supplied tactic
  hint <text>       — inject natural-language hint into next agent step
  status            — display current proof state
  quit              — exit
"""

from typing import Optional

from agent.proof_controller import ProofController
from utils.logger import setup_logger


class InteractiveSessionManager:
    def __init__(self, controller: ProofController):
        self.controller: ProofController = controller
        self._gen = None
        self._done: bool = False
        self.logger = setup_logger("InteractiveSession")

    #####################
    ## Public API      ##
    #####################

    def start(self, theorem_name: Optional[str] = None):
        """Initialize the proof session and run the REPL."""
        self.logger.debug(f"Starting interactive session: theorem={theorem_name!r}")

        preexisting = self._extract_and_reset_tactics()

        if not self.controller._init_proof_session(theorem_name):
            print("❌ Failed to initialize proof session.")
            return False

        self._gen = self.controller.step_generator()
        self._done = False

        if preexisting:
            print(f"🔄 Replaying {len(preexisting)} pre-existing tactic(s)...")
            self.logger.debug(f"Pre-existing tactics to replay: {preexisting}")
            for tactic in preexisting:
                self._do_user_tactic(tactic, silent=True)
                if self._done:
                    break

        self._display_state()
        if not self._done:
            print("Interactive mode. Commands: step, run, tactic <tac>, hint <text>, status, tree, quit")
            self._repl()

        self.controller._finish_proof(self.controller._tactics_with_states)
        return self.controller.is_successful

    #####################
    ## REPL            ##
    #####################

    def _repl(self):
        while not self._done:
            try:
                raw = input("autorocq> ").strip()
            except (EOFError, KeyboardInterrupt) as e:
                self.logger.debug(f"REPL interrupted: {e}")
                self._do_quit()
                return

            if not raw:
                continue

            cmd, _, arg = raw.partition(" ")
            self.logger.debug(f"User Command: {raw!r}")
            match cmd:
                case "step":
                    self._do_step()
                case "run":
                    self._do_run()
                case "tactic":
                    self._do_user_tactic(arg.strip())
                case "hint":
                    self._do_hint(arg.strip())
                case "status":
                    self._display_state()
                case "tree":
                    self._do_tree()
                case "quit":
                    self._do_quit()
                    return
                case _:
                    print(f"Unknown command: {raw!r}")
                    print("Available: step, run, tactic <tac>, hint <text>, status, tree, quit")

    #####################
    ## Commands        ##
    #####################

    def _do_step(self):
        result = self._advance_one()
        if result is None:
            return
        self._report(result)
        if result['type'] != 'done':
            self._display_state()

    def _do_run(self):
        goals_before = self.controller.coq.get_goal_str()
        while not self._done:
            result = self._advance_one()
            if result is None:
                return
            self._report(result)
            if result['type'] == 'done':
                return
            if result['type'] == 'rollback':
                self._display_state()
                return
            if result.get('proof_complete'):
                return
            current_goals = self.controller.coq.get_goal_str()
            if current_goals != goals_before:
                self._display_state()
                return

    def _do_user_tactic(self, tactic: str, silent: bool = False):
        if not tactic:
            print("Usage: tactic <tactic_string>")
            return

        if not tactic.endswith('.'):
            tactic += '.'

        subgoals_before = self.controller.coq.get_subgoals()
        goals_before = self.controller.coq.get_goal_str()
        hyps_before = self.controller.coq.get_hypothesis()

        success = self.controller.coq.apply_tactic(tactic)
        if not success:
            error = self.controller.coq.get_last_error()
            self.logger.debug(f"User Tactic failed: {tactic!r} — {error}")
            print(f"Tactic failed: {error}")
            return

        goals_after = self.controller.coq.get_goal_str()
        hyps_after = self.controller.coq.get_hypothesis()
        subgoals_after = self.controller.coq.get_subgoals()

        self.controller.global_step_id += 1
        tactic_with_state = self.controller._handle_successful_tactic(
            tactic, subgoals_before, subgoals_after,
            goals_before or '', goals_after or '',
            hyps_before or '', hyps_after or ''
        )
        tactic_with_state['source'] = 'user'
        # Do NOT append to _tactics_with_states; user tactics are
        # counted via _baseline_steps so the agent step sanity check stays valid.
        self.controller.successful_tactics.append(tactic)

        self.controller.tactic_history.add_successful_tactic(
            tactic=tactic,
            goals_before=goals_before or '',
            goals_after=goals_after or '',
            hypotheses_before=hyps_before or '',
            hypotheses_after=hyps_after or '',
            theorem_name=self.controller.current_theorem_name,
            step_number=self.controller.global_step_id,
            source='user'
        )

        self.controller._baseline_steps += 1
        self.logger.debug(f"User Tactic applied: {tactic!r}")

        if not silent:
            print(f"✅ Tactic applied: {tactic}")

        status = self.controller.coq.get_proof_completion_status()
        if status.get('is_complete') and status.get('qed_already_applied'):
            print("🎉 Proof complete!")
            self.controller.is_successful = True
            self._done = True
        elif not silent:
            self._display_state()

    def _do_hint(self, hint: str):
        if not hint:
            print("Usage: hint <text>")
            return
        self.logger.debug(f"User Hint queued: {hint!r}")
        self.controller._pending_hints.append(hint)
        print("Hint queued for next agent step.")

    def _do_tree(self):
        if self.controller.proof_tree is None:
            print("No proof tree available yet.")
            return
        print(self.controller.proof_tree.get_proof_tree_string())

    def _do_quit(self):
        self._done = True

    ###########################
    ## Internal helpers      ##
    ###########################

    def _extract_and_reset_tactics(self) -> list:
        """Extract and pop pre-existing tactics so _init_proof_session sees a clean state."""
        coq = self.controller.coq
        proof = coq.get_unproven_proof()
        if not proof or len(proof.steps) <= 1:
            return []

        tactics = [step.text.strip() for step in proof.steps[1:]]

        for _ in range(len(tactics)):
            coq.proof_file.pop_step(proof)

        coq.proof = coq.get_unproven_proof()
        return tactics

    def _advance_one(self):
        if self._gen is None or self._done:
            return None
        try:
            result = next(self._gen)
            if result.get('type') == 'done' or result.get('proof_complete'):
                self._done = True
            return result
        except StopIteration:
            self._done = True
            return {'type': 'done', 'success': self.controller.is_successful}

    def _display_state(self):
        goals = self.controller.coq.get_goal_str()
        hyps = self.controller.coq.get_hypothesis()
        print("=" * 50)
        print("Current proof state:")
        if hyps:
            print(f"  Hypotheses: {hyps}")
        if goals and goals != "No current goals":
            print(f"  {goals}")
        else:
            print("  No current goals.")
        print("=" * 50)

    def _report(self, result):
        t = result.get('type')
        if t == 'tactic':
            if result.get('success'):
                print(f"Agent applied: {result['tactic']}")
                if result.get('proof_complete'):
                    print("🎉 Proof complete!")
            else:
                print(f"Agent tactic failed: {result.get('tactic', '?')!r} — {result.get('error', '')}")
        elif t == 'rollback':
            if result.get('success'):
                print(f"Agent rolled back {result.get('distance', '?')} step(s).")
            else:
                print("Agent rollback failed.")
        elif t == 'done':
            if result.get('success'):
                print("🎉 Proof complete!")
            else:
                print("Session ended (max steps reached or proof failed).")
