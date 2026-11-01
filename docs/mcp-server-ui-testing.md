# UI-test protocol for the KeY MCP server

How the user-facing parts of the MCP-server feature — the status-line indicator, the settings
panel and the per-tool export checkboxes — are tested. The approach works **headless** (no
display, runs in CI) because KeY deliberately ships no UI-automation framework (no TestFX /
AssertJ-Swing): Swing components are constructed and driven on the event dispatch thread, mock
data is injected through small production seams, and panels are rendered to PNG via
`JComponent.print` into a `BufferedImage` for the documentation screenshots.

The test lives in `keyext.llm/src/test/java/org/key_project/key/llm/uitest/`.

## Harness components

| Class | Purpose |
|-------|---------|
| `McpUiTestHarness` | Shared helpers: `onEdt(…)` (run on the Swing EDT and wait), `resetSettings()` (clean `LlmSettings.INSTANCE` state), `mockTools()` (deterministic three-tool mock set), `all(root, type)` + `textOf(…)` (component-tree walk to find widgets without private-field access), and `render(…)` (headless PNG rendering). |
| `MockModelsServer` | A stub OpenAI-compatible endpoint on `127.0.0.1:<ephemeral>` answering `GET /openai/models` with a canned `{"data":[{"id":…}, …]}` JSON — the "mock responses from the server" that drive UI actions. |

### Mock-data and mock-response seams

* **Mock tool data**: `LlmToolsPanel(LlmSettings, Collection<? extends Tool>)` — the public
  no-tool constructor fills the rows from the built-in registry; this variant injects the rows
  shown by the panel (`McpUiTestHarness.mockTools()` supplies a deterministic set: an
  auto-approved proof tool, an auto-approved file tool and an ask-approved shell tool).
* **Mock server responses**: `MockModelsServer` answers the request performed by the "Fetch
  Models" button, and the UI updates the available-models list from the response.
* **Mock MCP client**: the tests drive the *real* SSE server started by the status bar with the
  SDK's `HttpClientSseClientTransport` (`initialize`, `listTools`, `callTool`), i.e. the same
  interaction an external MCP client would perform while the UI shows the endpoint.
* **Persistence seam**: `LlmStatusBar.maybeRestore()` is public so the "previously enabled server
  is restored on the next start" behavior is replaysable in a test.

### Headless rendering caveat

`Container.validate()` does not recurse into a component tree without native peers, so
`McpUiTestHarness.render` lays out the tree explicitly (top-down `doLayout` on every container)
before painting. Keep that in mind when rendering new panels headless.

## Automated test cases

Run them with:

```sh
./gradlew :keyext.llm:test --tests "org.key_project.key.llm.uitest.*"
```

| Test class | Steps and assertions |
|------------|----------------------|
| `LlmStatusBarUiTest` | 1. Toggle the status-bar button on the EDT → the SSE server binds, the endpoint label (`http://127.0.0.1:<port>/sse`) becomes visible, the toggle is selected and `mcpServerEnabled` is set. 2. With the UI up, an MCP client connects, lists the exported tools (`read_file` and the auto-approved test tool present, `run_command` absent) and calls the echo tool → the reply arrives while the status bar keeps showing the endpoint. 3. Toggle off → the server stops (a socket probe on the endpoint port fails), the label hides and the flag clears. 4. `maybeRestore()` replays a persisted enabled server. |
| `LlmToolsPanelExportUiTest` | With the mock tool set injected: the "export to MCP" checkboxes reflect the effective export rule (auto → checked, ask → unchecked); approval overrides recompute the default (without-approval ask tool → checked, with-approval/disabled → unchecked); explicit `mcpExportedTools`/`mcpNotExportedTools` win in both directions; clicking a checkbox writes the override set of the settings working copy; the permission radios still write the approval sets. |
| `LlmModelsFetchUiTest` | Points the settings working copy at `MockModelsServer`, clicks "Fetch Models" and awaits (polling the model, pumping the EDT) until the mocked model ids appear in `getAvailableModels()`. |
| `McpUiGuideTest` | Renders the documentation screenshots into `keyext.llm/build/ui-guide/` (see below) and guards that the endpoint label is visible while the server runs. |

## Screenshots for the documentation

`McpUiGuideTest` renders:

* `mcp-statusbar-off.png` — the status-line indicator, server off,
* `mcp-statusbar-on.png` — the indicator with the live endpoint label,
* `mcp-tools-export.png` — the Tools panel with the per-tool "export to MCP" checkboxes
  (the run values show explicit overrides in both directions),
* `mcp-server-settings.png` — the LLM settings panel including the "MCP server" section.

Regenerate them by running the guide test and copy the wanted files into `docs/images/mcp/`:

```sh
./gradlew :keyext.llm:test --tests "org.key_project.key.llm.uitest.McpUiGuideTest"
cp keyext.llm/build/ui-guide/*.png docs/images/mcp/
```

## Manual GUI protocol

For a full end-to-end check in the running application (`./gradlew key.ui:run`):

1. **Status line**: start KeY → the status line shows a disabled **MCP** toggle.
2. **Start**: click it → the toggle engages and the endpoint
   (`http://127.0.0.1:<port>/sse`) appears next to it.
3. **Client round trip**: point an MCP client (e.g. a Claude-Desktop-style `"url"` entry, or
   `npx @modelcontextprotocol/inspector`) at the endpoint → the client lists the exported tools
   and can invoke an auto-approved tool.
4. **Export overrides**: in *Settings → LLM Settings → Tools*, flip "export to MCP" on some tool,
   press OK, restart the server via the status line → the tool appears / disappears in the
   client's tool list accordingly.
5. **Auth token**: set a token under *LLM Settings → MCP server*, restart the server → requests
   without `Authorization: Bearer <token>` are rejected with `401`.
6. **Persistence**: leave the server running, close KeY, start KeY again → the server is restored
   automatically and the endpoint label reappears.
7. **Stop**: click the toggle → the endpoint disappears and clients can no longer connect.
