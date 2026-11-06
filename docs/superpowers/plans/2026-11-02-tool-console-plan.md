# Tool Console — Implementation Plan

*Date: 2026-11-02 · Spec: `docs/superpowers/specs/2026-11-02-tool-console-design.md`*

All code lives in module `keyext.llm`, package `org.key_project.key.llm` (dialog) — same module
as the existing LLM UI (`LlmPrompt`, `LlmToolsPanel`). Every new file carries the KeY GPL header
(Spotless enforces it). Tests are JUnit 5, run headless via `McpUiTestHarness` where Swing is
involved.

**Task 0 (investigation, no code):** confirm the production client construction used by the chat
session — find where `AgentLoop`'s `session.getMcpClient()` is created (likely
`BuiltInMCPClient` composed over `KeYAgentTools` in `LlmUtils`/session factory). The console must
reuse the same construction so approval settings are shared. Also confirm the `McpClient`
interface exposes `agents()`, `callTool`, `requiresApproval`, `allowWithoutApproval`.

## Task 1: `JsonSchemaForm` — schema ↔ form ↔ JSON

**File:** `keyext.llm/src/main/java/org/key_project/key/llm/JsonSchemaForm.java`

- Constructor `JsonSchemaForm(JsonSchema schema)` builds the Swing editor per property
  (see spec table): `string`→`JTextField`, `boolean`→`JCheckBox`, `number`/`integer`→text field,
  enum→`JComboBox`, `array`→`JTextArea` (one item per line), `object`/unknown/absent schema →
  `JTextArea` holding JSON.
- `String toArgumentsJson()` — serializes all editors into an arguments JSON object (empty
  strings → empty string values, booleans → true/false, arrays → JSON array of the non-blank
  lines, object editor → parsed JSON).
- `String fromArgumentsJson(String json)` — parses and fills the editors; returns an error text
  on invalid input, `null` on success (editors left untouched on error).
- Required fields marked `*` in their labels; `description` of each property as tooltip.
- Package-private getters to let tests reach editors; no business logic beyond mapping.

**Test:** `keyext.llm/src/test/java/org/key_project/key/llm/uitest/JsonSchemaFormTest.java`

- round trip per type: set editor values → `toArgumentsJson` equals expected JSON;
  `fromArgumentsJson` populates editors.
- invalid JSON → error text returned, editor state unchanged.
- schema with `required` list → labels carry `*`.
- `null`/empty schema → JSON fallback editor present.

## Task 2: `ToolApprovalPrompt` — approval seam

**File:** `keyext.llm/src/main/java/org/key_project/key/llm/ToolApprovalPrompt.java`

- `interface ToolApprovalPrompt { Decision ask(String tool, String arguments); }` with
  `enum Decision { ALLOW_ONCE, ALWAYS, DENY }`.
- Default implementation `ModalToolApprovalPrompt`: Swing modal confirm dialog
  (parent = console dialog) showing tool name + pretty-printed arguments and buttons
  Allow once / Always allow / Deny.
- The console consults `McpClient.requiresApproval(name)` **before** prompting; on `ALWAYS` it
  calls `McpClient.allowWithoutApproval(name)` before executing (identical to the chat flow's
  persistence).

**Test (inside Task 4's `ToolConsoleUiTest`):** recording prompt implementation; allow → call
executed; deny → no call and denial note in result pane; always → `allowWithoutApproval` invoked
on the mock client.

## Task 3: `ToolConsoleDialog` — the console UI

**File:** `keyext.llm/src/main/java/org/key_project/key/llm/ToolConsoleDialog.java`

- `ToolConsoleDialog(MainWindow owner, McpClient client)`; non-modal
  (`new JDialog(owner, "Tool Console", false)`), builds all UI on the EDT.
- **Tool tree**: `JTree` grouped by `ToolCategory` (ordinal), tools sorted by name — same
  ordering rule as `LlmToolsPanel`; leaf label `name [auto|ask]` from `requiresApproval`;
  search `JTextField` rebuilds the tree model (query matches name/category substring, all
  branches expanded).
- **Detail area**: description (wrapping, non-editable text area), `Forms | JSON` toggle
  (ButtonGroup of two `JToggleButtons`), the `JsonSchemaForm` panel, and — in JSON mode — a
  `JTextArea` with the current arguments JSON; switching modes syncs both directions (JSON →
  form on switch, errors reported inline).
- **Call**: builds JSON (form or textarea), runs the approval gate, then
  `callTool(name, json)` on a worker thread; Call disabled while running; on completion (EDT)
  the result pane shows `String.valueOf(result)` (null → "(no output)"), a ✓/✗ badge and the
  duration; `Throwable` → error text. History entry appended on every completed call.
- **Result pane**: `JTextArea`, monospaced, line+word wrap, scroll pane.
- **History**: in-memory ring buffer (20); `JList` with renderer `tool ✓ 12 ms`; selection loads
  tool + arguments back into the editor (only for tools still present).

## Task 4: `ToolConsoleAction` + wiring

**File:** `keyext.llm/src/main/java/org/key_project/key/llm/ToolConsoleAction.java`

- Follow the pattern of `StartLlmPromptForCurrentProofAction` (same base class/key-action
  conventions); text "Tool Console…", opens (and focuses) the shared non-modal dialog, creating
  it once per MainWindow with the production `McpClient` from Task 0.
- `LlmExtension.getMainMenuActions` returns the existing agent action **and** the console action.

**Test:** `keyext.llm/src/test/java/org/key_project/key/llm/uitest/ToolConsoleUiTest.java`

- mock `McpClient` (or `KeYAgentTools` seeded with `TestAgentToolProvider`'s mock tools) + the
  recording `ToolApprovalPrompt`;
- assertions: tree contains mock tools grouped by category; AUTO tools call without prompt; ASK
  tools honor the recorded decision; result pane + history updated; `allowWithoutApproval`
  persisted on ALWAYS; JSON mode round trip; headless PNG render of the dialog for eyeballing.

## Task 5: docs, format, full verification

- Short "Tool Console" section in `docs/LLM-Client-Extended.md` (what it is, menu path, that
  approvals are shared with the chat).
- `./gradlew :keyext.llm:spotlessApply`, then root `spotlessCheck`.
- `./gradlew :keyext.llm:test` — full module suite green (previous baseline: 217 + new tests).
- Manual smoke checklist (user, real GUI): `list_files` runs without prompt; `edit_file` with
  allow-once changes the file; `run_command` denied does nothing; an "Always allow" decision
  removes the prompt for the rest of the session and shows up in the tools settings panel.

## Commit strategy

1. `JsonSchemaForm` + test — after Task 1.
2. Console dialog + approval seam + action/wiring + UI tests + docs — after Tasks 2–4.
3. Format-only fixes folded into each commit (no separate spotless commits).

Branch stays linear; no pushes without an explicit request.
