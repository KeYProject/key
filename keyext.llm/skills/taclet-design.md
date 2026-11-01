---
name: taclet-design
description: Inspect, export and extend the rule set of a proof — taclets in and out.
enabled: true
allowedTools:
  - get_proof_context
  - list_branches
  - list_taclets
  - list_taclet_options
  - export_taclet
  - export_taclets
  - add_taclet
  - remove_taclet
  - tryclose
  - auto
  - ask_user
---

You are working with KeY's rule system (taclets). This covers inspecting the available rules,
adjusting taclet *options*, exporting rules for documentation, and — with approval — extending or
shrinking the rule set of a proof.

1. **Survey the rules.** `list_taclets` (optionally with a substring filter, e.g. `"quantifier"`,
   `"arith"`) shows the applicable taclets with their schematic shape. `list_taclet_options`
   lists the option groups (choices) of the proof with their selected and possible values — if a
   rule set behaves "strangely", an unusual option value is a likely cause.
2. **Export for reading.** Use `export_taclet` for a single rule and `export_taclets` (with a
   filter) for a family; the output is a parseable `\taclet` declaration. Quote it when discussing
   applicability — the declaration shows premises, assumptions and variable conditions exactly.
3. **Design a new taclet** when a rewrite or simplification is missing and the user asks for it:
   - Write the declaration in standard KeY syntax (`\taclet` with `\find`, `\replacewith`,
     assumptions, variable conditions). Keep it as narrow as possible — overly general taclets
     can loop or slow down every subsequent automation run.
   - Apply with `add_taclet`. It is registered *for future rule applications only*; existing
     sequents are not rewritten retroactively.
   - Validate immediately: run `auto` (or `tryclose` on a small goal) and check that the taclet
     was used, not something else. If the taclet misbehaves (loop, wrong application), remove it
     with `remove_taclet` and iterate.
4. **Housekeeping.** `remove_taclet` also cleans up experimental rules before handing the proof
   back; mention every rule you added or removed in your final report.

Notes:

- `add_taclet` and `remove_taclet` change the proof's rule set and require approval — explain the
  declaration (find/replace, assumptions) in one or two sentences before the call.
- Taclet bodies are logic: be precise about schemavariables and their sorts. If unsure about a
  sort or a variable condition, export a similar existing taclet first and follow its shape.
- Do not add a taclet for something a one-shot `rewrite_term` / `run_script` could do — taclets
  are for rules that will be reused.
