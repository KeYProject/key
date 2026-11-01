---
name: explore-goal
description: Sandboxed experimentation on a goal — probes and forks answer "what if" questions without touching the main proof.
enabled: true
allowedTools:
  - get_proof_context
  - list_branches
  - list_proofs
  - fork_proof
  - probe_add_formula
  - probe_edit_formula
  - explorative_add_formula
  - explorative_edit_formula
  - hide_sequent
  - focus_goal
  - auto
  - ask_user
---

You are exploring what makes a goal provable. The safe default is *sandboxed*: the main proof must
only be modified deliberately and with the user's explicit consent.

Tools and their guarantees:

- `probe_add_formula` / `probe_edit_formula` run the auto strategy on an **isolated side proof**
  built from the goal's sequent plus the hypothesis you supply. The main proof is never modified.
  They answer: "would this goal close if formula F were added / if occurrence O were replaced by
  F?" Use them freely — they are auto-approved and backgroundable.
- `fork_proof` registers an independent copy of a goal's sequent as a new proof (visible in
  `list_proofs`), addressable via the `proof` parameter. Experiment on the fork, keep the original
  untouched. Use this when one probe is not enough and you want to iterate.
- `explorative_add_formula` / `explorative_edit_formula` perform the same edit **in the main
  proof**: cut with the new formula, keep it on the current branch, disable the other cut branch.
  They *reframe the theorem* — the disabled branch must be pruned before the proof can close.
  They require approval: always state explicitly that this changes the main proof.

Recommended loop:

1. `get_proof_context` + `list_branches`; name the blocking conjecture `C`.
2. Probe the strongest version first: `probe_add_formula` with `C` (antecedent or succedent as
   fits). If `TRUE`, ask: is `C` a lemma we want in the final proof?
   - Yes → propose applying `explorative_add_formula` with `C` (and note the disabled branch).
   - No → probe the weaker variants the spec allows, or suggest proving `C` separately
     (`cut_formula` in the `prove-surgical` style).
3. If a formula *occurrence* is the problem (e.g. a too-strong specification instance), use
   `probe_edit_formula` to try replacements before touching anything.
4. For multi-step experiments use `fork_proof` and iterate on the fork; report the fork's
   identifier so the user can open it in the GUI.
5. Conclude with a clear statement: which hypothesis makes the goal provable, whether it is
   available in the specification, and what you changed in the main proof (if anything).

Notes:

- Goal targeting works as everywhere: `"branch"` (default), `"all"` (probes and forks accept it),
  or a 0-based index from `list_branches`.
- Never mark an explorative edit as "done" without mentioning the disabled branch — the proof only
  closes once that branch is pruned away.
- If no hypothesis you can think of makes the goal provable, that is a result too: report the
  failing probes and suspect the specification.
