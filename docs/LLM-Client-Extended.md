# LLM client module (`keyext.llm`) — architecture and API

## Overview

The Gradle module `keyext.llm` implements KeY's LLM integration (the **KeY-Agent**):
a dockable chat panel that talks to an OpenAI-compatible chat-completions endpoint,
can call tools (built-in proof tools and MCP tools), reads files from the Java model
in a sandbox, and maintains a per-proof conversation.

* End-user documentation: [`key-agent-doc.md`](../key-agent-doc.md) (getting started, input
  markup, skills and prompts, settings reference).
* This document describes the module's **architecture and programming API** for developers.

> **History.** This document previously described the prototype classes `LlmClient` /
> `LlmClientExtended` (a `Callable<Map<String,Object>>` returning raw JSON maps). Both were
> removed in commit `d87b9f710e` ("Complete the KeY-Agent LLM chat window…", Oct 2026) and
> replaced by the `AgentLoop` / `ChatCompletionsClient` design documented below.

## Module setup

* Package: `org.key_project.key.llm`, tool/MCP sub package `org.key_project.key.llm.mcp`.
* Java toolchain 21; registered in `settings.gradle` and in the CI test matrix
  (`.github/workflows/tests.yml`).
* `key.ui` depends on the module as `runtimeOnly` (`key.ui/build.gradle`): the extension is
  loaded via `ServiceLoader`, it is not meant to be compiled against.
* Two service registrations:
  * `META-INF/services/de.uka.ilkd.key.gui.extension.api.KeYGuiExtension` →
    `org.key_project.key.llm.LlmExtension`
  * `META-INF/services/org.key_project.key.llm.mcp.McpToolProvider` →
    `org.key_project.key.llm.mcp.KeYAgentToolsProvider` (consumed by `BuiltInMCPClient`)
* Dependencies: Apache HttpClient 5 (`org.apache.httpcomponents.client5:httpclient5`),
  Gson (`com.google.code.gson:gson`), SLF4J, and — currently declared but not yet imported —
  the MCP SDK (`io.modelcontextprotocol.sdk:mcp` 2.0.0, a candidate for future remote
  MCP transports; tool records use Jackson annotations that come in transitively).

## Architecture

```
                     Swing (EDT)                       background thread "keey-agent-loop"
┌──────────────────────────────────────┐   ┌───────────────────────────────────────────────────┐
│ LlmPrompt  (TabPanel, "KeY-Agent")   │   │  AgentLoop.begin(userText, proof, node, skill)    │
│  • history boxes, Prompt/Files tabs  │   │    ├─ PromptResolver.resolve   ($, @, / markup)   │
│  • AskUserBox / ApprovalBox          │──▶│    ├─ ExtendedPrompt.build     → AgentRequest     │
│  • renders AgentResult               │   │    ├─ ChatCompletionsClient.complete (HTTP)       │
│  • spawns AgentLoop runs             │◀──│    ├─ tool dispatch via BuiltInMCPClient          │
└──────────────────────────────────────┘   │    └─ bounded rounds → AgentResult                │
                                           └───────────────────────────────────────────────────┘
        LlmSession (per-proof state + LlmContext history)      LlmSettings (global, [llm])
```

One *turn* is a bounded tool-calling loop: the assembled request is sent, the model may
answer with tool calls, the loop executes them (with approval checks) and re-requests until
the model produces a final answer or a limit is reached. The turn ends synchronously with an
`AgentResult` that the UI renders; questions and approval requests *pause* the loop and are
resumed through dedicated methods.

## Session and conversation state

### `LlmSession`

Per-proof state object, attached to the `Proof` via `proof.register(LlmSession.class, …)`
(see `LlmUtils`). Holds everything needed to talk to the service and to assemble prompts:

```java
public static LlmSession createUsingSettings();            // session from LlmSettings defaults
public LlmSession(String apiEndpoint, String authToken, String model);

String getApiEndpoint() / setApiEndpoint(String);          // OpenAI-compatible base URL
String getAuthToken()  / setAuthToken(String);             // Bearer token
String getModel()      / setModel(String);
Set<URI> getSelectedFiles() / setSelectedFiles(Set<URI>);  // files ticked in the Files tab
BuiltInMCPClient getMcpClient();                           // tool registry of this session
LlmContext getContext();                                   // conversation history
boolean isAttachProofContext() / setAttachProofContext(boolean);
@Nullable String getActiveSkill() / setActiveSkill(@Nullable String);
```

### `LlmContext`

List of `LlmContext.LlmMessage` — the conversation history. `LlmMessage` is a nested record
`(role, content, toolCallId, toolCalls)` with OpenAI wire serialization (`toOpenAiMap()`),
which is what makes multi-round tool calling work: tool results are stored with their
`tool_call_id`, assistant tool calls with their `tool_calls` array.

```java
LlmMessage.user(String) / assistant(String) / assistant(String, List<Map<String,Object>>)
LlmMessage.tool(String toolCallId, String content) / system(String)
```

## The agent loop

`AgentLoop` drives one turn. It is a synchronous API — the caller owns threading
(the UI runs it on a background daemon thread per turn).

```java
public AgentLoop(LlmSession session, ChatCompletionsClient completions);

AgentResult begin(String rawUserText, @Nullable Proof proof,
                  @Nullable Node node, @Nullable Skill skill);  // resolve + build + loop
AgentResult answerQuestion(String answer);                      // resume after NeedsInput
AgentResult decideApproval(boolean allow, boolean always);      // resume after NeedsApproval
void cancel();                                                  // cooperative, between rounds
boolean isCancelled(); boolean isRunning();
boolean hasPendingQuestion(); boolean hasPendingApproval();
```

`AgentResult` is a sealed interface:

| Variant | Meaning |
|---|---|
| `Done(content, activities)` | final answer plus `ToolActivity` summaries (`ToolActivity(name, arguments, result)`) |
| `NeedsInput(Question)` | the `ask_user` tool fired; resume with `answerQuestion` |
| `NeedsApproval(ToolCallInfo)` | a tool needs approval; resume with `decideApproval` |
| `Failed(Throwable)` | turn aborted (HTTP error, disabled tool, …) |

Tool dispatch details (`AgentLoop.processBatch`): `ask_user` and `use_skill` are intercepted
by the loop itself (gated by the settings `allowAgentQuestions` / `agentCanUseSkills`);
`spawn_subagent` is intercepted, too (gated by `subagentsEnabled`) and runs a bounded child
loop via `SubagentRunner` (role whitelist + depth guard; `mode: parallel` fans out a `tasks`
array over a pool, serializing tool dispatch globally — see `docs/subagents.md`); `ask_llm`
is intercepted the same way (gated by `askLlmEnabled`) and `AskLlmRunner` sends a fresh
one-shot completion with a clean context (no history, no tools), returning the reply as the
tool result. Both intercepted calls run **outside** the global dispatch lock, so an LLM
round-trip never stalls parallel sub-agents or other sessions' tool calls — and since they
never dispatch tools themselves, no nested locking is possible. Every
other call goes through `session.getMcpClient()`. If `requiresApproval(name)` holds, the loop
returns `NeedsApproval`; otherwise the tool is executed and the result is appended to both
the internal wire thread and `session.getContext()`. `always` approvals are remembered via
`BuiltInMCPClient.allowWithoutApproval`.

## HTTP transport

`ChatCompletionsClient` abstracts a single chat-completion call:

```java
public interface ChatCompletionsClient {
    Map<String, Object> complete(LlmSession session, AgentRequest request) throws Exception;
}
```

`DefaultChatCompletionsClient` is the production implementation (Apache HttpClient 5):
it POSTs to `<endpoint>/openai/chat/completions` with `Authorization: Bearer <token>`, and a
payload containing `model`, `messages`, `tools` (+ `tool_choice=auto`), optional
`temperature` and `max_tokens` — each switch controlled by the *send temperature* /
*send max output tokens* settings. A throwaway HTTP client is created per call.
`Util` provides the small helpers used by the settings dialog (`Util.httpGet` for
`<endpoint>/openai/models`).

## Prompt assembly

`ExtendedPrompt.build(session, proof, …)` assembles the full `AgentRequest`
(model, wire messages, tools, temperature, max tokens, `maxToolRounds`):

1. **System prompt** — `KeYAgentPrompts.SYSTEM_PROMPT` (editable in the settings), plus the
   instructions of the active `Skill`, if any.
2. **Proof context** — a text block produced by `ProofContextCollector`
   (`proofName`, `proofStatus`, `sequentText`, `openGoalsSummary`, `computePath`,
   `modelInfo`), included when `attachProofContext` is on; sizes are capped by the
   *max proof-context* settings.
3. **File attachments** — files selected in the session, read through `FileAccess`
   (sandboxed to the model directory with a path-traversal guard): text files are inlined as
   fenced code blocks, images as base64 data URLs; counts and sizes are capped. The sandbox root
   falls back to the initial source file's directory and then to the working directory for proofs
   without a Java model; skipped directories (`.git`, `build`, …) are excluded from listings.
4. **History** — the tail of `session.getContext()`, capped by the *max history* settings.
5. **User prompt** — the raw input after `PromptResolver` markup resolution.

`PromptResolver` implements the input markup (documented for users in
`key-agent-doc.md`, §4): context tokens `$seq`, `$goals`, `$proof`, `$proofName`,
`$computePath`, `$model`, `$classpath`, `$bootClasspath`, `$selectedFiles`; file references
`@path`; and the directives `/skill:NAME`, `/prompt:NAME`, `/skills`, `/prompts`.
`AutocompleteInput` (a `JTextPane`) + `AutocompleteProviders` provide the popup (`$`, `@`, `/`
triggers) and Ctrl+Space expansion used by the panel: the popup is sized to its content (at least
the input width, resizable via a corner grip), dropped sequent terms are inserted verbatim-wrapped
(`` ` ``, or ```` ```key ```` fences for multi-line content) by a custom `TransferHandler`, and
```key fences are highlighted with the KeY lexer (`LexerHighlighter.KeYLexerHighlighter`). On the
drag source side, `CurrentGoalViewListener` leaves the cursor to the DnD system (it then reflects
the drop target's acceptance) and `PosInSequentTransferable` provides the whole sequent as the
string flavor when the sequent view selection is the sequent itself.

## Tools and MCP

Tool schemas are modeled as records with OpenAI-compatible serialization:
`Tool(type, FunctionDefinition, ApprovalRequirement)` (enum `AUTO`/`ASK`),
`FunctionDefinition(name, description, parameters)` and `JsonSchema` (builder API).

```java
public interface McpClient {
    List<Tool> getTools();                  // advertised to the model
    Object callTool(String toolName, String arguments) throws Exception;  // arguments = JSON
    boolean isClosed();
    void close();
}

public interface McpToolProvider {
    List<McpClient> get();                  // ServiceLoader bootstrap
}
```

* `BuiltInMCPClient` is the registry facade used by every session: it aggregates all
  `McpClient`s found via `ServiceLoader` (`McpToolProvider`), filters disabled tools from
  `LlmSettings`, implements the approval policy (`requiresApproval`,
  `allowWithoutApproval`, `resetApproval`) and throws `McpToolNowAllowedException` for
  disabled tools.
* `KeYAgentTools` (registered via `KeYAgentToolsProvider`) aggregates the built-in tools,
  which are contributed by `AgentToolProvider`s discovered through the Java `ServiceLoader`
  (service file `META-INF/services/...AgentToolProvider`; providers live in
  `org.key_project.key.llm.mcp.tools`): `get_proof_context`, `list_files`, `read_file`,
  `file_info`, `run_command` (gated by `ShellSafetyPolicy` blocklist, timeout and output
  caps), `ask_user`, `use_skill`, the delegation and self-consultation tools
  `spawn_subagent`, `get_subagent_logs`, `ask_llm` (intercepted by the agent loop; see
  `docs/subagents.md`), the proof-script tools `tryclose` and `auto`, and the
  taclet-management tools `list_proofs`, `list_taclets`, `list_taclet_options`,
  `export_taclet`, `export_taclets` (bounded bulk export), `add_taclet` / `remove_taclet`
  (the latter two modify a proof's rule set and require approval; they delegate to
  `TacletOperations`). Plugins add tools by registering another `AgentToolProvider`. The tool
  metadata (name, description, parameter schema, approval) is available via
  `KeYAgentTools.agents()` / `agent(String)` and `toolsMarkdown()`, and the `list_tools`
  tool dumps the Markdown documentation of the whole tool set on demand. The same documentation
  is also available from a headless `main`: `KeYAgentTools [--json]` prints the Markdown
  document (or the OpenAI-format tool list).
* `McpClientStdio` is a **reference implementation** for talking to external MCP servers
  over stdin/stdout (JSON-RPC 2.0, protocol version 2024-11-05, 30 s timeouts). It wraps an
  already-started `Process` (`initialize()` then `getTools()`/`callTool`), but is currently
  used only in examples — the session's registry contains in-process clients only.

**Extending KeY-Agent with own tools:** implement `McpClient` (+ optional `McpToolProvider`),
declare the provider in
`META-INF/services/org.key_project.key.llm.mcp.McpToolProvider` and add the module to the
classpath; `BuiltInMCPClient` picks it up automatically, and the Tools settings page shows the
new tools with their approval requirement.

## Threading model

* All UI construction and rendering happens on the Swing EDT. `LlmPrompt` spawns one daemon
  thread per turn/resume and runs `AgentLoop` synchronously on it — including the blocking
  HTTP call, tool invocations, and shell commands. Results are marshaled back with
  `SwingUtilities.invokeLater`.
* `AgentLoop.cancel()` is cooperative: it takes effect between rounds and after the current
  HTTP call.
* The settings' *Fetch Models* button uses a `SwingWorker` around `Util.httpGet`.
* Caveat: the proof-script tools (`tryclose`, `auto`) execute `ProofScriptEngine` on the
  agent thread, i.e. they touch live proof state off the EDT (KeY's mediator is not
  thread-safe; a long-term fix may need to marshal script execution onto the EDT).

## Error handling

| Scenario | Behavior |
|---|---|
| HTTP / endpoint error | `AgentResult.Failed(Throwable)` rendered as an error box |
| Disabled tool called | `McpToolNowAllowedException` from `BuiltInMCPClient.callTool` |
| Tool execution failure | error text returned to the model as the tool result |
| File too large / too many | skipped, warning in the request log |
| Path outside model directory | rejected by `FileAccess.resolveInModel` |
| Shell command | blocklist regexes (`ShellSafetyPolicy`), timeout (`shellTimeoutSeconds`), output capped |

## Persistence and settings

* `LlmSettings` (singleton `INSTANCE`) stores user preferences in the `[llm]` section of the
  proof-independent settings file (`<keyConfig>/proofIndependentSettings.json`):
  `apiEndpoint` (default `https://ki-toolbox.scc.kit.edu/v1`), `authToken`, `defaultModel`
  (`azure.gpt-4.1-mini`), `availableModels`, `systemPrompt`, `maxToolRounds` (8),
  `allowAgentQuestions`, `agentCanUseSkills`, `subagentsEnabled`, `askLlmEnabled` (true),
  `maxSubagentTurns` (8),
  `maxSubagentDepth` (2), `maxParallelSubagents` (4),
  `sendTemperature`/`temperature` (0.2),
  `sendMaxOutputTokens`/`maxOutputTokens` (4096), `attachProofContext`,
  `proofContextMaxSequents` (3), `proofContextMaxChars` (8000), `maxHistoryMessages` (30),
  `maxHistoryChars` (32000), `maxFileAttachments` (10), `maxFileSizeKB` (64),
  `maxFileContentChars` (8000), `maxModelListingEntries` (1000), `shellEnabled`,
  `shellTimeoutSeconds` (30), `shellMaxOutputChars` (65536), `shellBlockedPatterns`,
  `toolsDisabled`, `allowedToolsWithApproval`, `allowedToolsWithoutApproval`,
  `promptLibraryPaths`/`skillLibraryPaths` (library search path, empty = default directory),
  `autoScrollOutput`, `showToolActivity`.
* Prompt and skill libraries are file-backed Markdown (`FileBackedLibrary`) along a configurable
  search path: by default under `<keyConfig>/llm/prompts` and `<keyConfig>/llm/skills`, otherwise
  the directories of `promptLibraryPaths`/`skillLibraryPaths` (in order, first occurrence of a
  name wins, new entries are created in the first directory; entries support `~`, `$(pwd)` and
  relative paths): one `<name>.md` per entry with a YAML
  front matter (`MarkdownFrontMatter`, keys `name`/`description` and for skills `enabled`/
  `allowedTools`) and the template/instructions as the body; legacy `<name>.json` files are
  migrated on first access. Edited by the lightweight settings sub-panels (`PromptLibraryEditor`,
  `SkillLibraryEditor`: file list, *New* creates a template file, *Edit* opens the file in the
  system editor, editable search path); records are `Prompt(name, description, template)` and
  `Skill(name, description, instructions, allowedTools, enabled)`; export/import shares the whole
  library as a ZIP of `.md` entries (`LibraryZip`).
* The conversation history itself is kept per proof in memory (`LlmSession.getContext()`) and
  is not persisted.

## UI classes

| Class | Role |
|---|---|
| `LlmExtension` | `KeYGuiExtension` wiring: registers settings, the `LlmPrompt` tab, the *Proof → LLM → Open LLM prompt* menu action (Ctrl+K) and the settings providers (`LLM Settings` with children `Tools`, `Prompts`, `Skills`) |
| `LlmPrompt` | the chat panel; renders `LlmPromptModel` boxes (INPUT/OUTPUT/ERROR), hosts `AskUserBox`/`ApprovalBox`, `AutocompleteInput` (prompt input only, no separate Files tab) |
| `LlmSettingsUI` | main settings page incl. *Fetch Models* (`SwingWorker`, timeouts in `Util`, HTTP status in the error dialog) |
| `LlmToolsPanel` | per-tool approval/disablement table |
| `LibraryEditorPanel` + editors | lightweight library editing: file list, template creation via *New*, external editing via *Edit*, `Delete`/`Reload`/export/import and the search path editor |
| `SubagentRunner` + `subagents.*` | sequential + parallel sub-agent delegation (`spawn_subagent` child loop, role registry/whitelist, depth guard, parallel fan-out with serialized tool dispatch); see `docs/subagents.md` |
| `AskLlmRunner` | fresh one-shot completion behind `ask_llm` (clean context, no tools; intercepted by the agent loop and the sub-agent child loop, runs without the dispatch lock) |
| `SubagentLog` | per-session, bounded record of sub-agent runs (role, mode, per-task status/tools), exposed via the `get_subagent_logs` tool and rendered in the chat panel's tool-activity summary |

## Testing

`keyext.llm/src/test/java/org/key_project/key/llm/` contains headless unit tests for the
core: `AgentLoopTest` (bounded rounds, pause/resume), `ExtendedPromptTest` (request
assembly), `PromptResolverTest` (markup), `LlmContextTest` (wire serialization),
`BuiltInMCPClientTest` (registry/approvals), `ShellSafetyPolicyTest`,
`SchemaSerializationTest`, `AutocompleteInputTest`/`AutocompleteProvidersTest`,
`LibraryEditorPanelsTest`, `LibrarySearchPathTest` (multi-directory search path),
`mcp/KeYAgentToolsCommandTest` (proof-script tool mapping),
`SubagentLoopTest` (delegation, parallel fan-out, depth guard), `AskLlmTest`
(self-consultation: fresh completion in parent and child loop, model/system override, disabled
gate, error paths) and
`mcp/AgentToolsTest` (modular discovery, metadata API, `list_tools` documentation, CLI
rendering);
`TestMcpToolProvider` and `TestAgentToolProvider` are service-loader test fixtures.

## Author

@author Alexander Weigl

## Version

@version 2.0 (10/16/26) — rewritten for the `AgentLoop` architecture

## License

This file is part of KeY and is licensed under the GNU General Public License Version 2 (GPL-2.0-only).
