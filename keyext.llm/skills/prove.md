---
name: prove
description: Close the open goals of the current proof with the automatic tools, escalating step by step.
enabled: true
allowedTools:
  - get_proof_context
  - list_branches
  - list_proofs
  - assert_open_goals
  - list_files
  - read_file
  - file_info
  - tryclose
  - auto
  - run_macro
  - run_smt
  - simplify_goal
  - ask_user
---

You are proving with KeY. Work strictly in this order and stop as soon as the proof is closed:

1. **Orient.** Call `get_proof_context` and `list_branches` to see the open goals, their branch
   labels and leading formulas. If several proofs are loaded, `list_proofs` tells you which one
   is selected; address another proof only on request (parameter `proof`).
2. **Understand before running.** If the goal mentions classes or methods you have not seen, use
   `list_files` and `read_file` on the Java model first — the proof obligation usually becomes
   obvious from the source and its specifications.
3. **Escalate the automation:**
   1. `tryclose` on the targeted goal — cheap, finishes trivial goals.
   2. `run_smt` — cheap for arithmetic-heavy or combined goals; solver-valid goals are closed
      automatically.
   3. `auto` with a generous step limit (`20000`–`100000`) on the targeted goal.
   4. `run_macro` with a targeted macro: `symbex` to finish symbolic execution, `simp-int` /
      `simp-heap` / `simp-upd` to simplify a specific kind of formula, `split-prop` for
      propositional splitting, `tryclose-sidebranches` to clean up side branches,
      `transcendental` for trigonometric/exponential goals, `autopilot` as the last resort.
4. **Re-orient after every automation step.** Each tool reports `"<tool>: N goal(s) closed, M open
   goal(s) remain"`. Never run the same automation twice in a row on the same goal unless the
   setting changed.
5. **Report.** Finish with the remaining goals, quoted sequent(s), and a one-sentence diagnosis of
   why they resist (e.g. missing loop invariant, non-linear arithmetic, unresolved case split).

Notes:

- Target goals precisely: `goal: "branch"` (default) acts on the first open goal of the current
  branch, `goal: "all"` on every open goal, an integer on the 0-based index from `list_branches`
  (negative counts from the end).
- `auto`, `run_macro`, `run_smt` and `tryclose` are backgroundable — prefer keeping long runs in
  the foreground of a *single* turn rather than launching several concurrent automations.
- `simplify_goal` applies the one-step simplifier (`oss`) to exactly one goal; use it to clean up
  a sequent before reading it, never as a proof attempt.
- If the goal seems unprovable as stated (e.g. wrong specification), say so and ask the user via
  `ask_user` instead of hammering the automation.
