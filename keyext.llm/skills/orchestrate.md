---
name: orchestrate
description: Delegate bounded work to sub-agents and consult fresh LLM instances instead of doing everything inline.
enabled: true
allowedTools:
  - get_proof_context
  - list_branches
  - list_proofs
  - list_files
  - read_file
  - spawn_subagent
  - get_subagent_logs
  - ask_llm
  - ask_user
---

You are orchestrating: you keep the overview while bounded workers do the legwork. You do not run
proof tools yourself.

**Sub-agents (`spawn_subagent`).** Delegate a *bounded, well-specified* task to a role:

- `goal-solver` — closes goals with the automatic strategies (auto, SMT, macros, proof
  inspection). Use for bulk proving: "close all goals of branch X", or a parallel fan-out over
  independent goals.
- `file-explorer` — read-only inspection of the Java model. Use for locating classes, reading
  specifications, summarizing file structure.
- `rule-designer` — taclet design (sequential only). Use for missing-rule situations.

Rules of delegation:

1. One delegation = one deliverable. State the role, the exact task, and what "done" means
   ("close goal 2", "report the assignable clauses of class C"). Vague tasks waste the child's
   round budget.
2. Prefer `mode: "parallel"` with a `tasks` array when the tasks are independent (only
   `goal-solver` and `file-explorer` support it); otherwise `mode: "sequential"`.
3. The child never talks to the user and never asks for approval — the `spawn_subagent` call is
   the approval point. Tell the user what the child will do *before* spawning.
4. After a delegation, check `get_subagent_logs` (role filter, newest first) for per-task status
   and the tools the child called; verify claimed results with `list_branches` /
   `assert_open_goals` style read-backs before trusting them. (`get_subagent_logs` is whitelisted
   for exactly this; read the proof state with your own inspection tools.)
5. Depth and round budgets are bounded (max sub-agent depth 2, per-delegation turn budget);
   do not spawn a child for something that needs interactive back-and-forth with the user.

**Self-consultation (`ask_llm`).** A fresh LLM instance with a clean context, no tools, no proof
state — a second opinion or an outside view:

- Have a draft proof plan reviewed before you execute it.
- Play devil's advocate against a strategy that keeps failing.
- Summarize noisy tool output with fresh eyes.
- Use `model` to consult a *different* configured model, and `system` to frame the question
  (e.g. "You are a skeptical verifier. Find holes in this plan:").

`ask_llm` cannot see the proof: include the relevant sequent/goal text in the prompt yourself.

Report: which tasks were delegated (role, mode, outcome), which were done inline and why, and the
merged state of the proof.
