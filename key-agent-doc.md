# KeY-Agent

The KeY-Agent is a chat-based assistant integrated into the KeY GUI that supports interactive
program verification and theorem proving with the help of a large language model. It can inspect
the current proof state, read the files of the current Java model, and run safe shell commands —
while keeping the user in control through per-call approval and question dialogs.

The module lives in `keyext.llm` (main classes `org.key_project.key.llm.*`). The chat window is
deliberately thin: all prompt assembly happens in `ExtendedPrompt`, an agent turn is driven by
`AgentLoop`, the input markup is resolved by `PromptResolver`, and a per-session `TurnScheduler`
turns queued messages and background results into turns (see [section 11](#11-architecture-code-pointers)).

---

## 1. Getting started

1. Open the **KeY-Agent** panel (KeY GUI, menu *Proof → LLM → Open LLM prompt*, or Ctrl+K).
2. Open *Settings → LLM Settings* and configure a connection:
   - **API Base URL** — an OpenAI-compatible endpoint (default
     `https://ki-toolbox.scc.kit.edu`; e.g. `https://litellm.scc.kit.edu/v1` for the KIT LiteLLM
     proxy). The concrete operation URLs (chat completions, model list) are derived from this
     base, so both the Open WebUI (`/openai/…`) and the OpenAI/LiteLLM (`/v1/…`) conventions
     work.
   - **Auth Token** — your API key/token.
   - **Available Models** / **Default model** — choose the model to use (`Fetch Models` reads the
     list of available models from the endpoint).
3. Type a question or request in the input box and press **Ctrl+Enter** to send it.

If no model is configured, the panel still works for anything that does not require the LLM, e.g.
local commands such as `/skills` (see [Input markup](#4-input-markup)).

---

## 2. The chat panel

```
┌──────────────────────────────────────────────────────────────────────────┐
│ [attach proof context] [Prompts]   [Clear history] [Stop] [2 queued]     │
├──────────────────────────────────────────────────────────────────────────┤
│ history of inputs / answers / errors / tool activity                    │
│  · right-click a message for actions (e.g. "into input")                │
│  · a running tool call is shown as a live row with [Background] [Cancel]│
│  · backgrounded calls appear as job rows while they run                 │
├──────────────────────────────────────────────────────────────────────────┤
│ multi-line prompt input with completion             "Ctrl+Enter to send"│
│  · drag terms/sequents from the sequent view into the prompt            │
│  · ```key fenced blocks are highlighted with the KeY syntax             │
└──────────────────────────────────────────────────────────────────────────┘
```

![The KeY-Agent panel, docked as a tab on the right side of the main window, stacked with the
Source view](docs/images/agent/llm-panel.png)

- **Sending.** `Ctrl+Enter` sends the current input (there is no send button). `Shift+Enter` and
  plain Enter insert a line break. Input is **always accepted**: while a turn runs or is parked,
  your message is queued and processed in order (see [Backgrounding](#74-backgrounding)); the
  toolbar shows the number of queued messages.
- **Running a turn.** The *Stop* button cancels the *active* turn only (queued messages are not
  affected). Only one turn runs at a time.
- **Files.** The files of the current Java model are referenced with `@path` (see
  [section 4.2](#42-file-references-path)); file references are attached to the conversation and
  reported by the `$selectedFiles` token.
- **Tool activity.** After a turn, the tool calls that were executed are summarized in the chat
  (can be turned off in the settings). While a call runs it is shown as a live row with
  *Background*/*Cancel* buttons (see [section 7.4](#74-backgrounding)); calls you moved into the
  background are tracked as job rows until they finish.

---

## 3. Prompt memory and context

- Each proof has its own conversation session; the chat history persists between turns of the same
  proof. Messages are bounded by the *max history messages/chars* settings.
- The agent loop (see [section 7](#7-the-agent-loop-and-tools)) keeps a bounded number of tool
  rounds per turn.

---

## 4. Input markup

The input box understands a small markup language, resolved by `PromptResolver` before the message
is sent to the model.

### 4.1 Context tokens `$name`

| Token             | Expands to                                                        |
|-------------------|-------------------------------------------------------------------|
| `$seq`            | the current sequent                                               |
| `$goals`          | the open goals                                                    |
| `$proof`          | proof status (open/closed goals, node count)                      |
| `$proofName`      | name of the current proof                                         |
| `$computePath`    | applied rules from the root to the selected node                  |
| `$model`          | Java model directory and class paths                              |
| `$classpath`      | Java class path                                                   |
| `$bootClasspath`  | Java boot class path                                              |
| `$selectedFiles`  | the files attached in this chat                                   |

Without a loaded proof, proof-dependent tokens resolve to explicit placeholders (e.g.
`[unknown token $seq]` is used for a token that cannot be resolved at all).

### 4.2 File references `@path`

`@src/MyClass.java` embeds the contents of the file as a code block. Paths are relative to the
Java model directory; for proofs without a Java model (e.g. `.key` problems) the directory of the
initial source file, or the working directory, is used instead.

### 4.3 Commands and directives `/…`

| Input        | Meaning                                                                  |
|--------------|--------------------------------------------------------------------------|
| `/skills`    | lists all defined skills; answered locally in the chat (no LLM needed)   |
| `/prompts`   | lists all defined prompts; answered locally in the chat (no LLM needed)  |
| `/skill:name`| activates skill `name` for the current turn (directive is stripped)      |
| `/prompt:name`| extends the message with the template of prompt `name`                   |

`/skills` and `/prompts` as the whole message are handled without calling the model at all.

### 4.4 Autocompletion popup

Typing a trigger character opens the completion popup:

- `$` — context tokens (see table above)
- `@` — files of the current Java model
- `/` — `/skills`, `/prompts`, `/skill:…`, `/prompt:…`, and entries to open the library
  management in the settings

| Key            | Effect                                    |
|----------------|-------------------------------------------|
| `Enter` / `Tab`| accept the selected entry                 |
| `↑` / `↓`      | move the selection                        |
| `Esc`          | close the popup                           |
| mouse click    | accept the clicked entry                  |

The popup never steals the keyboard focus, so you can select an entry and keep typing. It fits
its content (no wrapped entries), is at least as wide as the input box, and grows up to a limit;
dragging the handle in its bottom-right corner resizes it, and the chosen size is kept.

### 4.5 Drag and drop from the sequent view

Terms, formulas or the whole sequent can be dragged from the sequent view into the prompt input.
While dragging, the mouse cursor follows the drop target (it shows a copy mark over the input).
The dropped text is inserted at the drop position wrapped in verbatim marks: single-line content
in backticks (`` `a + b` ``), multi-line content in a fenced block with the KeY language marker:

````
```key
seq ::  a <= b  ==>  b <= a
```
````

The printing of the dropped content follows the keyboard modifiers held during the drop:

- default: pretty-printed as in the sequent view (current notation settings and term label
  visibility)
- **Shift** held: pretty-printed with safe settings — ASCII operators only (no unicode symbols),
  package prefixes shown, all term labels shown
- **Ctrl** held: non-pretty-printed term structure

While a term or sequent is dragged, the hint below the prompt shows which printing the drop will
produce; when no drag is active, the hint shows the send shortcut (**Ctrl+Enter**) and points to
the completion trigger characters (`$`, `@`, `/`).

### 4.6 KeY syntax highlighting

Fenced blocks marked with the `key` language (as produced by drag and drop) are highlighted in
the prompt input with the KeY lexer — keywords, terms and formulas get the usual KeY colors.

### 4.7 Inline expansion (Ctrl+Space)

Pressing **Ctrl+Space** right after a fragment replaces the fragment with its *currently resolved*
content, so you can edit the actual value instead of the reference:

- `$seq` becomes the literal sequent text
- `@src/Main.java` becomes the embedded file content
- `/skills` becomes the current listing, `/prompt:name` the rendered template

Unknown `$tokens` and bare activation directives (`/skill:name`) are left untouched.

---

## 5. Skills

A **skill** is a named bundle of instructions that is appended to the system prompt while active,
optionally restricting the tool set. It is stored as a Markdown file whose metadata lives in a
YAML front matter and whose body holds the instructions (under `llm/skills/<name>.md`):

```markdown
---
name: optics
description: focus on arithmetic overflow proofs
enabled: true
allowedTools:         # empty/absent = no restriction
  - list_files
  - read_file
  - get_proof_context
---

Pay special attention to integer overflow; check the goal sequent before choosing a rule.
```

- Skills are managed in **Settings → LLM Settings → Skills**: the stored skills are listed by
  name and description. `New` only asks for the file name and creates a Markdown template file
  with prefilled front matter; `Edit` (or a double click) opens the file in your system editor,
  `Delete` removes the selected skill from the search path and `Reload` picks up external
  changes. `Export...`/`Import...` share the whole library as a ZIP archive of its Markdown
  files (see [section 9](#9-settings-reference-settings--llm-settings)). The directories holding
  the files (the *search path*) are editable right below the list.
- If a skill restricts `allowedTools`, only those tools are offered to the model while the skill
  is active.
- The agent itself can activate a skill through the `use_skill` tool — this is **off by default**
  (setting *Agent may use skills*).

### 5.1 Ready-made skills shipped with KeY

The repository ships a curated set of skills in [`keyext.llm/skills/`](../keyext.llm/skills/);
each one activates a coherent subset of the tool set and carries the matching workflow
instructions:

| Skill            | Scope                                                                     |
|------------------|---------------------------------------------------------------------------|
| `prove`          | close the open goals with the automatic tools (`tryclose` → `run_smt` → `auto` → targeted `run_macro`), read the Java model when needed |
| `prove-surgical` | manual proof work on resistant goals — cuts, quantifier instantiation, witnesses, term rewriting, sequent hygiene, `run_script` |
| `explore-goal`   | sandboxed "what if" experiments — probes and `fork_proof` first, explorative edits (which reframe the theorem) only with explicit consent |
| `code-review`    | read-only review of the Java model and its specifications                  |
| `taclet-design`  | inspect taclets and options, export rules, add/remove taclets with approval |
| `orchestrate`    | delegate bounded work to sub-agents (`spawn_subagent`, roles, logs) and consult fresh LLM instances (`ask_llm`) instead of doing everything inline |
| `tool-tour`      | onboarding: the agent explains its own tool set via `list_tools` and suggests a fitting skill |

To use them, add the directory to the skill library search path (Settings → LLM Settings →
Skills, right below the list — e.g. `/path/to/keyext.llm/skills`) or import the files via
`Import...`. The skills are validated by a unit test (`ShippedSkillsTest`), which also keeps
their `allowedTools` whitelists in sync with the built-in tool set.

---

## 6. Prompts

A **prompt** is a named, reusable message template, stored as a Markdown file with a YAML front
matter (under `llm/prompts/<name>.md`):

```markdown
---
name: prove-method
description: prove the postcondition of the selected method
---

Prove the selected method. Collect $proof and $seq, then try to close the goals.
```

Templates are inserted from the *Prompts* toolbar button or via `/prompt:name`; markup inside the
template is resolved like normal input. Prompts are managed in **Settings → LLM Settings →
Prompts** like the skills ([section 5](#5-skills)): `New` creates a template file for the given
name, `Edit` opens the file in the system editor, `Delete`/`Reload`/`Export...`/`Import...` and
the editable search path work the same.

---

## 7. The agent loop and tools

A turn is driven by `AgentLoop`: the assembled request is sent to the model, tool calls in the
response are executed, the results are fed back, and the loop continues until a final answer, a
question, an approval request, an error, or the maximum number of tool rounds is reached
(`max rounds`, default 8).

The built-in tool set (`KeYAgentTools`):

| Tool                | Category       | Approval | Backgroundable | Description                                                         |
|---------------------|----------------|----------|----------------|---------------------------------------------------------------------|
| `get_proof_context` | Proof          | auto     |                | a text block describing the current proof state                     |
| `tryclose`          | Proof          | auto     | ✓              | apply the `tryclose` proof-script command (TryClose macro) to the current branch, all open goals, or a goal by index |
| `auto`              | Proof          | auto     | ✓              | apply KeY's automatic proof strategy ('Auto' button) with an arbitrary step limit |
| `run_macro`         | Proof          | auto     | ✓              | run a curated proof macro (symbolic execution, propositional splitting, simplification, transcendental SMT, auto-pilot, …) on the targeted goals |
| `run_smt`           | Proof          | auto     | ✓              | run the SMT solvers on the targeted goals; goals the solver proves valid are closed |
| `simplify_goal`     | Proof          | auto     |                | apply KeY's one-step simplifier (`oss`) to a single goal            |
| `apply_rule`        | Proof          | ask      |                | apply a named taclet or built-in rule (see `list_taclets`) to a goal, with an optional term/formula occurrence and schema-variable instantiations |
| `instantiate_quantifier` | Proof      | ask      |                | instantiate a quantified formula with a term (`instantiate`)        |
| `witness_constant`  | Proof          | ask      |                | introduce a fresh Skolem witness constant for a quantified formula (`witness`) |
| `cut_formula`       | Proof          | ask      |                | cut on a formula (`cut`): splits the goal into a case and its negation |
| `expand_definitions`| Proof          | ask      |                | unfold method-definition and class-invariant axioms (`expand`)      |
| `rewrite_term`      | Proof          | ask      |                | find and apply a rewrite taclet transforming a term into another (`rewrite`) |
| `run_script`        | Proof          | ask      |                | run a short guarded sequence (≤ 8 steps) of the whitelisted proof commands on targeted goals |
| `probe_add_formula`          | Proof          | auto     | ✓              | probe: run auto on an isolated side proof of a goal plus an added formula (antecedent or succedent); report if the goal then closes; the main proof is never modified |
| `probe_edit_formula`         | Proof          | auto     | ✓              | probe: run auto on an isolated side proof of a goal with a formula occurrence replaced; report if the goal then closes; the main proof is never modified |
| `explorative_add_formula`    | Proof          | ask      |                | explorative: add a formula to the goal via a cut and disable the other cut branch — the theorem is reframed around the added formula |
| `explorative_edit_formula`   | Proof          | ask      |                | explorative: replace a formula occurrence via a cut, hide the old occurrence and disable the other cut branch — the theorem is reframed around the replacement |
| `fork_proof`        | Proof          | ask      |                | create an independent copy (fork) at a goal's sequent, registered for the `proof` parameter — for side experiments |
| `list_branches`     | Proof          | auto     |                | read-only: list the open goals in the order the `goal` indexes use, with branch labels and leading formulas |
| `assert_open_goals` | Proof          | auto     |                | read-only: check that the proof has the expected number of open goals |
| `hide_sequent`      | Proof          | ask      |                | hide the formulas of a sequent pattern (declutters the goal; `hide`)     |
| `unhide_sequent`    | Proof          | ask      |                | re-insert previously hidden formulas (`unhide`)                          |
| `focus_goal`        | Proof          | ask      |                | keep only the formulas of a sequent pattern, hide all others (`focus`)   |
| `let_abbrev`        | Proof          | ask      |                | introduce a term abbreviation for the proof's abbreviation table (`let`/`letf`) |
| `list_proofs`       | Proof          | auto     |                | enumerate all open proofs with an identifier usable in the proof tools' `proof` parameter |
| `list_files`        | Files          | auto     |                | bounded listing of the files of the current Java model              |
| `read_file`         | Files          | auto     |                | read a text file of the model directory (respects size limits)      |
| `file_info`         | Files          | auto     |                | metadata (size, last modified, kind) of a file                      |
| `run_command`       | Shell          | ask      | ✓              | run a shell command in the model directory (blocklist + approval)   |
| `list_taclets`      | Taclets        | auto     |                | list the taclets available for a proof (optional substring filter) |
| `list_taclet_options` | Taclets     | auto     |                | list the taclet options (choices) of a proof with their selected and possible values |
| `export_taclet`     | Taclets        | auto     |                | export a taclet as a parseable KeY rule declaration |
| `export_taclets`    | Taclets        | auto     |                | export several or all taclets of a proof as parseable declarations (optional filter, capped output) |
| `add_taclet`        | Taclets        | ask      |                | register a new taclet for a proof from a `\taclet` declaration (future rule applications only) |
| `remove_taclet`     | Taclets        | ask      |                | remove a taclet from a proof's rule set (past rule applications are not affected) |
| `ask_user`          | Interaction    | auto     |                | ask the user a question; the turn pauses until it is answered       |
| `use_skill`         | Interaction    | auto     |                | activate a user-defined skill by name (only if enabled in settings) |
| `ask_llm`           | Sub-agents     | auto     | ✓              | send a prompt to a fresh LLM instance (clean context, no tools) and deliver the reply back to the agent (only if enabled in settings) |
| `spawn_subagent`    | Sub-agents     | ask      | ✓              | delegate a task to a sub-agent (only if enabled in settings)        |
| `get_subagent_logs` | Sub-agents     | auto     |                | list the recorded sub-agent runs (role, mode, per-task status and the tools that were called) |
| `list_tools`        | Documentation  | auto     |                | dump the Markdown documentation of every available tool (metadata + this list) |

**Goal targeting and proof selection.** The proof-manipulation tools (`tryclose`, `auto`,
`run_macro`, `run_smt`, `simplify_goal`, `apply_rule`, `instantiate_quantifier`,
`witness_constant`, `cut_formula`, `expand_definitions`, `rewrite_term`, `hide_sequent`,
`unhide_sequent`, `focus_goal`, `fork_proof`, and the exploration family `probe_add_formula`,
`probe_edit_formula`, `explorative_add_formula`, `explorative_edit_formula`) share two
parameters:

- `goal` — `"branch"` (default; the first open goal of the current branch), `"all"` (every open
  goal; single-goal surgery tools reject it), or a 0-based goal index (negative = from the end).
- `proof` — an optional identifier from `list_proofs` (index or name); without it the currently
  selected proof is used. This lets the agent work on a non-selected proof, e.g. while the user
  interacts with another one.

`run_script` targets each ordered step individually with its own `goal` (branch default or an
index). `let_abbrev` is proof-wide (no goal). `list_branches` shows the open goals in exactly the
order the `goal` indexes use, so indices can be picked from it directly.

Every proof tool reports its outcome uniformly as `"<tool>: N goal(s) closed, M open goal(s)
remain"` (plus `- the proof is closed` when it finishes).

**Sandboxed exploration, explorative edits and forking.** The exploration tools come in a 2×2
family. The probes `probe_add_formula` and `probe_edit_formula` answer "is this goal provable if a
formula were added / replaced?" by running the auto strategy on an *isolated side proof*
(constructed via KeY's `SideProofUtil` machinery from the goal's sequent plus the formula) and
report `TRUE` only if that side proof closes — the main proof is never modified, so they are safe
to approve automatically. The explorative tools `explorative_add_formula` and
`explorative_edit_formula` perform the same operation *in the main proof* following the
exploration-mode recipe (cut with the new formula, hide the old occurrence on the kept branch,
disable the other cut branch); they **reframe the theorem** around the added/replaced formula, so
the disabled branch should be pruned before the proof can close, and they require approval.
`fork_proof` goes the other way: it *persists* the copy by registering a new proof (root sequent =
the targeted goal's sequent) that appears in `list_proofs` and can be worked on through the
`proof` parameter, leaving the original untouched.

**Categories.** Every tool carries a `category` (Proof, Files, Shell, Taclets, Interaction,
Sub-agents, Documentation, General) and a `backgroundable` flag — pure KeY-side *metadata*: the
model only ever sees the standard OpenAI name/description/parameters. The category groups and
sorts the tools in the [Tools panel](#tools-sub-panel-llm-settings--tools) and in the Markdown
documentation; the backgroundable flag controls whether a running call may be moved into the
background (see [section 7.4](#74-backgrounding)). Tools contributed by external MCP clients
default to *General* / not backgroundable.

The tool set is **modular and self-describing**: every tool is contributed by an
`AgentToolProvider` that is discovered via the Java `ServiceLoader` (service file
`META-INF/services/org.key_project.key.llm.mcp.AgentToolProvider`) and aggregated by
`KeYAgentTools`. Plugins add tools by providing another provider — no changes to the core
classes are needed. The metadata of all tools (name, description, parameter schema, default
approval, category, backgroundable) is available programmatically via `KeYAgentTools.agents()` /
`agent(name)` and as an OpenAI-format tool list via `getTools()`; `list_tools` renders it as
Markdown for the model (grouped by category, one `## <Category>` section each).

The same documentation can be printed from the command line without a GUI (useful for keeping
the docs in sync or for scripts):

```sh
java -cp <classpath> org.key_project.key.llm.mcp.KeYAgentTools        # Markdown document, grouped by category
java -cp <classpath> org.key_project.key.llm.mcp.KeYAgentTools --json # OpenAI-format tool list, extended with "category" and "backgroundable"
```

### 7.1 Questions

The agent can ask you a question (e.g. about a case split or a design decision), which pauses the
turn until you answer. Turn this off with *Allow the agent to ask questions*.

### 7.2 Approval and the safety model

- File access tools are **read-only**, restricted to the current Java model directory, and run
  without approval.
- The proof-script tools run the corresponding KeY proof-script commands (i.e. the same actions
  as *Apply Script* / the *Auto* button): `tryclose`, `auto`, `run_macro`, `run_smt`,
  `simplify_goal` and the sandboxed probes `probe_add_formula`/`probe_edit_formula` (side proofs;
  the main proof stays untouched) are approved by default so the agent can actually prove — you
  can move them to *with approval* in the Tools panel to review each invocation. The goal-surgery
  tools `apply_rule`, `instantiate_quantifier`, `witness_constant`, `cut_formula`,
  `expand_definitions` and `rewrite_term`, the sequent-editing tools `hide_sequent`,
  `unhide_sequent`, `focus_goal`, `let_abbrev`, the composed `run_script`, `fork_proof` and the
  explorative tools `explorative_add_formula`/`explorative_edit_formula` (which reframe the
  theorem via cut) mutate the proof and require approval by default. The listed single-goal tools
  act on one goal (`"branch"` or an index) and reject `"all"`.
- `add_taclet` and `remove_taclet` change the rule set of a proof and therefore require approval
  by default; inspection tools (`list_taclets`, `list_taclet_options`, `export_taclet`,
  `export_taclets`) do not.
- `run_command` *always* requires per-call approval, and commands matching the configured
  **blocklist** (e.g. `rm -rf /`, `sudo`, `chmod -R` on system directories, `curl … | sh`) are
  refused regardless of approval.
- Each tool call's approval/disabled behavior can be customized in the *Tools* panel
  (**Settings → LLM Settings → Tools**): tools can be disabled entirely, or moved to *with
  approval* / *without approval (always)*.
- The tools exposed to the model never include the ones you disabled.

### 7.3 Sub-agents (`spawn_subagent`)

A **sub-agent** is a delegated, bounded tool loop with a role-specific system prompt and a
restricted tool whitelist. The `spawn_subagent` tool takes a role, a task (or a `tasks` array
in parallel mode) and a mode:

```
spawn_subagent { "role": "goal-solver", "task": "Close all open goals of the current proof.",
                 "mode": "sequential" }
```

- **Roles** are registered via the Java `ServiceLoader` (service file
  `META-INF/services/org.key_project.key.llm.subagents.SubagentRoleProvider`). Built-in roles:
  `goal-solver` (automatic strategies + proof inspection), `file-explorer` (read-only file
  inspection) and `rule-designer` (taclet design, sequential only).
- **Whitelist:** the child only sees (and may only call) the tools of its role's whitelist,
  intersected with the tools enabled in the Tools panel. The child never asks the user and never
  pauses for approval — the `spawn_subagent` call itself (ask-approval by default) is the
  approval point.
- **Bounded:** each sub-agent has a tool-round budget (role-specific, or `max sub-agent turns`)
  and a maximum nesting depth (`max sub-agent depth`); delegations inside a sub-agent are
  depth-guarded, cancellations of the parent turn propagate into running children.
- **Parallel fan-out:** `mode: parallel` solves a `tasks` array of independent tasks
  concurrently (only for roles marked `parallelAllowed`, e.g. `goal-solver` and `file-explorer`,
  not `rule-designer`). One worker thread runs per task on a pool capped by
  `max parallel sub-agents`; tool *dispatch* is serialized through a global lock, because KeY
  proofs and the GUI mediator are not thread-safe — the speed-up is in the overlapping LLM
  round-trips, while every call that touches the proof stays mutually exclusive. The merged
  result is one tool message listing `(1) …`, `(2) …` per task. Nested spawns run outside the
  lock, so parallel sub-sub-agents cannot deadlock.
- **Result:** the child's final answer (which should start with
  `KEY_AGENT_RESULT {"summary": "…"}` for machine-readable outcomes) is returned to the
  delegating agent as the tool result.
- **Observability:** every finished delegation is recorded in a per-session log (role, mode,
  timing, and per task the status, round count and called tools). The read-only
  `get_subagent_logs` tool renders it for the model (newest first, optional `limit` and `role`
  filter), the chat panel shows the per-task lines indented under the `spawn_subagent` row in
  the tool-activity summary, and *Clear history* clears the log together with the conversation.

**Self-consultation (`ask_llm`).** The `ask_llm` tool lets the agent think *about itself*: it
takes a prompt, sends it to a **fresh** instance of the configured LLM — a one-shot completion
with a clean, empty context (no conversation history, no tools, no proof context) — and
delivers the reply back to the caller. That makes it a round trip around the agent's own
reasoning: review a draft plan, play devil's advocate against a proposed proof strategy,
summarize noisy tool output through fresh eyes, or get a second opinion from another model via
the optional `model` override (an optional `system` prompt for the fresh context is supported
too). Like `spawn_subagent` the call is intercepted by the agent loop — it deliberately runs
*outside* the global dispatch lock, because an HTTP round-trip must not stall parallel
sub-agents — but unlike a sub-agent it never touches the proof or any other tool; it is a
read-only consultation approved automatically (`auto`) and marked backgroundable. It is gated
by the *Agent may consult the LLM* setting (default on), and sub-agent child loops may use it
as well (if their role whitelists it).

### 7.4 Backgrounding

Long-running calls (`auto` proof search, `run_command` builds/tests, `spawn_subagent`
delegations, `ask_llm` reflection queries) can be **moved into the background** while they
run:

- While a foreground tool call runs, its live row in the chat panel shows a **Background**
  button. Clicking it hands the running call to a background job: the agent parks that turn and
  immediately continues with your queued messages.
- The call keeps executing on the shared tool-dispatch pool; while it runs it is shown as a job
  row in the chat (with *Cancel job* — cancelling marks the job, the call itself runs to
  completion, and its result is reported to the agent as cancelled).
- When the call finishes, its output is enqueued and the parked turn resumes with it (a
  *"In the background"* box marks where the turn parked).
- Only tools marked **backgroundable** offer the button (by default `auto`, `tryclose`,
  `run_command`, `run_macro`, `run_smt`, `spawn_subagent`, `ask_llm`, `probe_add_formula`,
  `probe_edit_formula`); per-tool overrides and the
  concurrency limit live in the [Tools panel](#tools-sub-panel-llm-settings--tools). While a
  turn is parked on a question or an approval, further
  prompts are *deferred* (they do not start new turns); while it is parked on a background job
  they are processed normally.
- Backgrounding needs no extra user input — the call is already executing anyway; only the turn
  that awaits it pauses. The queued messages, the answers to questions and the decisions on
  approvals of parked turns all flow through the same per-session turn queue and are processed
  in order.

---

## 8. Proof context

Two independent ways to give the agent the current proof state:

1. **Attach proof context** — the toolbar checkbox (and *Attach proof context by default* in the
   settings, default off) attaches a block describing the current proof state to every message.
2. **`$…` tokens / `get_proof_context`** — resolved each time, e.g. `$seq`, `$goals`, or the
   `get_proof_context` tool. The tool is always available.

The amount of context can be bounded with *Max proof-context sequents* and *Max proof-context
chars*.

---

## 9. Settings reference (Settings → LLM Settings)

All values are **optional**; the defaults work out of the box. The settings dialog shows
*LLM Settings* as a tree node in the left-hand navigation with three dedicated sub-panels:

```
LLM Settings
├── Tools      tool approval / disablement
├── Prompts    prompt template library editor
└── Skills     skill library editor
```

![The LLM Settings page of the settings dialog](docs/images/agent/llm-settings.png)

The main *LLM Settings* panel holds the sections below; **Tools**, **Prompts** and **Skills**
are edited in their own panels.

### Connection
| Setting | Default |
|---|---|
| API Base URL | `https://ki-toolbox.scc.kit.edu` |
| Auth Token | — |
| Default model | `azure.gpt-4.1-mini` |
| Available models | editable list; `Fetch Models` pulls it from the endpoint |

### Agent behavior
| Setting | Default |
|---|---|
| System prompt | built-in KeY-Agent prompt |
| Allow the agent to ask questions | `true` |
| Max tool rounds | `8` |
| Max background jobs | `4` |
| Send temperature | `false` (`temperature` 0.2) |
| Send max output tokens | `false` (`4096`) |
| Agent may use skills (`use_skill`) | `false` |
| Agent may consult the LLM (`ask_llm`) | `true` |
| Agent may spawn sub-agents (`spawn_subagent`) | `false` |
| Max sub-agent turns (per delegation) | `8` |
| Max sub-agent depth (nesting) | `2` |
| Max parallel sub-agents (per parallel run) | `4` |

### Context and history
| Setting | Default |
|---|---|
| Attach proof context by default | `false` |
| Max proof-context sequents | `3` |
| Max proof-context chars | `8000` |
| Max history messages / chars | `30` / `32000` |

### Files
Max attached files `10`, max file size `64` KB, max file content chars `8000`,
max model listing entries `1000`.

### Shell commands
| Setting | Default |
|---|---|
| Enable shell commands (`run_command`) | `true` |
| Shell timeout (seconds) | `30` |
| Shell max output chars | `65536` |
| Blocked shell patterns | built-in blocklist, one regex per line |

### Tools (sub-panel: LLM Settings → Tools)

![Tool approval settings: one permission row per tool](docs/images/agent/llm-settings-tools.png)
The tools are grouped into **category sections** (Proof, Files, Shell, Taclets, Interaction,
Sub-agents, Documentation, General — in that order, tools by name within a section). One row per
tool shows a short explanation, a radio group selecting its permission — **Default** (the tool's
own behavior, `auto` or `ask`), **With approval** (always ask), **Without approval (always)** or
**Disabled** (not sent to the model) — and a **may run in background** checkbox. Read-only tools
default to `auto`, `run_command` to `ask`; the background checkbox follows the tool's metadata
(default on for `auto`, `tryclose`, `run_command`, `run_macro`, `run_smt`, `spawn_subagent`,
`ask_llm`, `probe_add_formula`, `probe_edit_formula`; overriding it adds/removes the tool in the
`backgroundToolsEnabled`/`backgroundToolsDisabled` settings). While such a call runs it can
be moved to the background, the agent then continues with your queued messages and the result is
delivered when the call finishes (see [section 7.4](#74-backgrounding)). The number of concurrent
background jobs is capped by *Max background jobs* (Agent behavior section).

### User interface
Auto-scroll output (`true`) and show tool activity (`true`).

### Prompts / Skills (sub-panels)
Lightweight editors for the user libraries described in [section 5](#5-skills) and
[section 6](#6-prompts): the entries are shown as a selectable list (name + description). `New`
asks only for the file name and creates a `<name>.md` template with prefilled front matter
(metadata and a placeholder body), `Edit` (or a double click) opens the file in the system
editor — with a plain text dialog as fallback when no desktop integration is available — and
`Delete` removes the selected entry from all search path directories. `Reload` picks up external
changes. `Export...` saves the whole library as a ZIP archive of its Markdown files (one
`<name>.md` per entry), `Import...` merges such an archive back in (new entries are added;
entries with an existing name are only overwritten after you confirm, otherwise they are kept).
Below the list the **search path** is editable: an ordered list of directories holding the
files — the first occurrence of a name wins, new files are created in the first directory.
Entries may use `~` (home directory), `$(pwd)` or relative paths (working directory); an empty
list selects the default directory (see [section 10](#10-storage)). Changes are saved
immediately.

---

## 10. Storage

User-defined prompts and skills are stored as **Markdown files with a YAML front matter**. By
default they live in the versioned KeY configuration directory (`llm/prompts` and `llm/skills`),
e.g. `~/.key/v3.1/llm/prompts/<name>.md` for KeY 3.1. The search path of each library can be
configured in its settings panel (settings `promptLibraryPaths` / `skillLibraryPaths`, see
[section 9](#9-settings-reference-settings--llm-settings)); the directories are searched in
order, the first occurrence of a name wins and new files are created in the first directory.
The front matter holds the metadata (`name`,
`description`, and for skills also `enabled` and `allowedTools`); the Markdown body is the prompt
template, respectively the skill instructions. Legacy `<name>.json` files from older KeY versions
are converted to the Markdown format automatically on first access and then removed. The chat
history and selected models are part of the proof session and are not persisted as files.

---

## 11. Architecture (code pointers)

| Concern             | Class                                              |
|---------------------|----------------------------------------------------|
| Chat panel (thin UI)| `org.key_project.key.llm.LlmPrompt`                |
| Agent turn driver   | `org.key_project.key.llm.AgentLoop`                |
| Turn scheduling     | `org.key_project.key.llm.TurnScheduler` (worker thread + `TurnScheduler.TurnListener` / `ToolObserver`) |
| Message queue       | `org.key_project.key.llm.TurnQueue` (user prompts, answers, approvals, background results) |
| Background jobs     | `org.key_project.key.llm.BackgroundJobRegistry` + `BackgroundJob` |
| Tool dispatch       | `org.key_project.key.llm.ToolDispatcher` (dispatch pool + proof-state lock) |
| Request assembly    | `org.key_project.key.llm.ExtendedPrompt`           |
| Input markup        | `org.key_project.key.llm.PromptResolver`           |
| Autocompletion      | `org.key_project.key.llm.AutocompleteInput` + `AutocompleteProviders` |
| Built-in tools      | `org.key_project.key.llm.mcp.KeYAgentTools`        |
| Shell safety        | `org.key_project.key.llm.ShellSafetyPolicy`        |
| Proof context       | `org.key_project.key.llm.ProofContextCollector`    |
| Settings            | `org.key_project.key.llm.LlmSettings` / `LlmSettingsUI` / `LlmToolsPanel` |
| Skill library       | `org.key_project.key.llm.SkillLibrary` + `Skill`   |
| Prompt library      | `org.key_project.key.llm.PromptLibrary` + `Prompt` |
| Sub-agents          | `org.key_project.key.llm.SubagentRunner` (loop) + `org.key_project.key.llm.subagents.SubagentRegistry` / `SubagentRole` / `BuiltInSubagentRoles` (roles) |
