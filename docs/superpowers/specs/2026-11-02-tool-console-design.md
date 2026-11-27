# Tool Console — Design

*Date: 2026-11-02 · Status: draft for review*

## Problem

The KeY-Agent tools (~25, registered via `AgentToolProvider`s and exposed through
`KeYAgentTools`/`BuiltInMCPClient`) are well covered by metadata tests (schemas, categories,
approval requirements) and by headless semantic tests of extracted core logic. What is missing is
**end-to-end verification against the real environment**: most tool bodies resolve their target
through the selected proof / model directory and can only be meaningfully executed inside the
running GUI. A headless harness cannot construct that environment (the `MainWindow` singleton is
the coupling), and API-backed tools need the configured endpoint anyway.

## Goal

A **manual, interactive tool console** inside KeY ("a Swagger UI in Swing"): pick a tool, compose
arguments, call it against the live environment (open proof, real settings), inspect exactly what
the model would receive. This is the manual e2e path; automated CI e2e is explicitly out of scope
for this design.

## Decisions (from the brainstorming session)

1. **Primary goal**: manual interactive testing (not CI automation).
2. **Call composition**: generated parameter forms **plus** a raw-JSON expert mode, both kept in
   sync.
3. **Approval**: ASK-tools show a real approval dialog (same policy and persistence as the agent
   chat — never a silent bypass).
4. **Placement**: a "Tool Console…" main-menu action opening a **non-modal dialog**, so it stays
   open while working with proofs.
5. Execution on a worker thread; **in-memory call history** (last 20) for quick re-runs.
6. Cut (YAGNI): backgroundable execution (use the chat for that), persisted history.

## Architecture

The console is a **thin Swing client over the `McpClient` interface** (`BuiltInMCPClient` in
production, mock in tests). It uses exactly the entry points the agent loop uses:

| Console concern | MCPClient API used |
|---|---|
| Tool list (grouped by `ToolCategory`) | `agents()` |
| Parameter form | `AgentTool.parameters()` (`JsonSchema`), `description()`, `approval()` |
| Approval gate | `requiresApproval(name)`, `allowWithoutApproval(name)` for "always" |
| Execution | `callTool(name, json)` |

Because the console calls through the same object graph as the chat's tool dispatcher, approvals
made here carry over to agent sessions and vice versa, and the result text is byte-for-byte what
the model would receive. The dialog receives the `McpClient` via constructor injection so tests
can supply a mock.

## UI

```
┌──────────────────────────────────────────────────────────────┐
│ [search]  ┌─ tool tree (grouped by category, badge auto/ask)┐ │
│           └─────────────────────────────────────────────────┘ │
│ description of selected tool                  [Forms|JSON]    │
│ ┌─ generated parameter form (or raw JSON in expert mode) ───┐ │
│ └───────────────────────────────────────────────────────────┘ │
│                                             [Call]            │
│ ┌─ result (monospaced, wrapping, scrollable) ───────────────┐ │
│ └───────────────────────────────────────────────────────────┘ │
│ last calls: edit_file {…} ✓ 3 ms · run_command {…} ✗          │
└──────────────────────────────────────────────────────────────┘
```

- **Tool tree**: rebuilt from the search query; ordering identical to `LlmToolsPanel`
  (category ordinal, then tool name); each leaf shows an `auto`/`ask` badge from the effective
  approval policy.
- **Form/JSON toggle**: two grouped toggle buttons. Forms → JSON on call; JSON → fields when
  switching to Forms (parse problems are reported inline, never crash).
- **Result pane**: raw tool output; a ✓/✗ badge with duration; "Error: …" strings and exceptions
  both land here (exceptions rendered as the error text the model would see).
- **History**: last 20 calls (tool, args, outcome, duration); clicking an entry loads tool +
  arguments back into the editor.

## Form generation rules (`JsonSchema`)

| Schema | Editor |
|---|---|
| `string` | text field |
| `boolean` | checkbox (unchecked default) |
| `number` / `integer` | text field with number parsing |
| enum (`enumValues`) | combo box |
| `array` | multiline text area, one item per line → JSON array of strings |
| `object` / unknown / absent | JSON text area for the value |

Required fields (when `required()` is present) are marked with `*`; parameter descriptions become
tooltips. The form is built per selected tool and disposed with the dialog.

## Approval flow

Before executing a tool with `requiresApproval(name) == true`, the console shows a **modal**
confirmation listing tool name and arguments with the three choices of the chat's approval box:

- **Allow once** — run this call,
- **Always allow** — run and persist via `allowWithoutApproval(name)`,
- **Deny** — no call; the result pane notes the denial.

The prompt is behind a small interface (`ToolApprovalPrompt`) so tests can record decisions instead
of opening dialogs. The modal dialog is the default implementation; the chat's *inline* approval
box stays chat-specific.

## Execution model

Calls run on a **worker thread** (the Call button is disabled while running; a "running…" state is
shown; the result is delivered on the EDT). This matches the chat's tool dispatcher, which also
executes tool bodies off the EDT. The console does not implement backgrounding; long-running calls
block the Call button only, not the rest of the UI.

## Components and files

| Unit | File | Purpose |
|---|---|---|
| `JsonSchemaForm` | `keyext.llm/.../llm/JsonSchemaForm.java` | `JsonSchema` ↔ Swing form ↔ arguments JSON |
| `ToolApprovalPrompt` | `.../llm/ToolApprovalPrompt.java` | approval decision seam (interface + modal default) |
| `ToolConsoleDialog` | `.../llm/ToolConsoleDialog.java` | the console UI over an injected `McpClient` |
| `ToolConsoleAction` | `.../llm/ToolConsoleAction.java` | main-menu action; opens the non-modal dialog |
| wiring | `.../llm/LlmExtension.java` | add the action to `getMainMenuActions` |
| `JsonSchemaFormTest` | `keyext.llm/src/test/.../uitest/JsonSchemaFormTest.java` | round trips per schema type |
| `ToolConsoleUiTest` | `keyext.llm/src/test/.../uitest/ToolConsoleUiTest.java` | construction with mock tools, approval gating, call flow, history; PNG render |

## Testing

- `JsonSchemaFormTest`: per-type value → JSON assertions; JSON → form; invalid JSON is reported,
  form state preserved; absent schema falls back to JSON editing.
- `ToolConsoleUiTest` (headless, `McpUiTestHarness`): dialog builds with a mock `McpClient` +
  mock tools; tool tree populated and grouped; ASK-tools route through the recorded approval
  prompt (allow → call executed, deny → not); results and history updated on the EDT; PNG render
  for visual inspection.
- Manual smoke test (documented): open console, `list_files` (auto, no prompt), `edit_file`
  (ask → prompt → allow → file changed), `run_command` with **Deny** (no execution).

## Out of scope

- Automated CI end-to-end runs of the tool bodies (needs the GUI-coupling refactor of
  `ProofSelector`; a separate topic).
- Persisted history, backgrounding, per-tool favorites, MCP-exported external tools beyond what
  the registry exposes.
