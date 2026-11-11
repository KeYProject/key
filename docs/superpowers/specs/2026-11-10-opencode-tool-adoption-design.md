# OpenCode Tool Adoption — Design

Date: 2026-11-10 · Branch: `weigl/llm` · Status: approved (user, 2026-11-10)

## Goal

Align the KeY-Agent's standard tool layer with OpenCode's tool design (names, parameter
shapes, camelCase, defaults) and adopt the full OpenCode tool set, including web access
and scripting. A model familiar with OpenCode should need no retraining to drive the KeY
agent.

## Decisions (user-approved)

1. **Full OpenCode set**: rename/reshape the standard tools and add `write`, `grep`,
   `webfetch`, `websearch`, `execute`. No `patch` (absent from current OpenCode), no
   `sessionID` on sub-agents (harness concept; KeY tracks sessions internally).
2. **camelCase parameters** (`oldString`, `replaceAll`, `caseSensitive`, …) exactly like
   OpenCode.
3. **Gating**: `webfetch`/`websearch` run without approval (AUTO); `execute` is ASK.
4. **execute** = JDK JShell in a worker thread; a `tools` facade is the default API; a
   settings toggle *Unrestricted execute* (default off) unlocks the full classpath
   ("ultimate fun and unsoundness"). True confinement (child JVM) is future work.
5. **Single adoption, staged commits**, clean break: old names are removed, no aliases
   kept. Old `file_info` is dropped (no OpenCode analog; `read` on a directory lists it).

## Tool mapping

| New | Schema (defaults) | Replaces / notes |
|---|---|---|
| `read` | `path*`, `offset?` (1-based line), `limit?` (lines, default 2000, cap 2000) | `read_file`; dir → entry listing; truncated output ends with "N more lines" hint; `maxFileSizeKB` still applies |
| `glob` | `pattern*` (glob, default `"**"`), `path?`, `hidden?` (false), `limit?` (100) | `list_files`; `FileSystem.getPathMatcher` over sandbox walk |
| `grep` | `pattern*` (regex), `path?`, `include?` (file glob), `literal?` (false), `caseSensitive?` (true), `limit?` (100 matches) | new; ripgrep-style `path:line: text` over sandbox text files |
| `edit` | `path*`, `oldString*`, `newString*` (≠ oldString), `replaceAll?` (false) | `edit_file`; + new differs-check; ASK |
| `write` | `path*`, `content*` | new; parent dirs, overwrite, sandboxed, ASK |
| `shell` | `command*`, `workdir?` (relative to model root), `timeout?` (ms, default 120000), `background?` (false) | `run_command`; blocklist + ASK |
| `question` | `questions*: [{ question*, header* (≤30 chars), options* [{label* (1–5 words), description}], multiple? }]` | `ask_user`; Swing dialog per question, free-text always available |
| `skill` | `id*` | `use_skill` |
| `subagent` | `agent*` (role), `description*` (3–5 word label), `prompt*`, `model?` | `spawn_subagent`; `get_subagent_logs`/`ask_llm` stay KeY-specific |
| `webfetch` | `url*`, `format?` (markdown/text/html, default markdown), `timeout?` (s, ≤120, default 30) | new, AUTO; http(s) only, 2 MB cap; HTML→Markdown via jsoup (new dependency) |
| `websearch` | `query*` | new, AUTO; DuckDuckGo Lite HTML (no API key), endpoint configurable |
| `execute` | `code*` | new, ASK; JShell, timeout 60 s default, bounded output; `tools` facade via same dispatcher; **must dispatch outside the global dispatch lock** (like `ask_llm`) or facade calls deadlock |

Dropped: `file_info`, `patch`, `subagent.sessionID`.

## Runtime integration

- `ToolCategory` gains `WEB` and `SCRIPTING` (standard tier, never MCP-exported); enum
  order PROOF, FILES, SHELL, WEB, SCRIPTING, TACLETS, INTERACTION, SUBAGENTS,
  DOCUMENTATION, GENERAL. Always-advertised standard set grows 11 → 15.
- `AgentLoop` interception follows the existing pattern: `question` parses the new schema
  into the extended `Question` model (header, label/description options, multiple) and
  still pauses via `AgentResult.NeedsInput`; `skill`/`subagent` are renames plus the new
  required `description` and optional `model` (passthrough like `ask_llm`).
- Settings: `unrestrictedExecute` (default off, danger-styled toggle) and
  `webSearchEndpoint` (default DDG Lite). No on/off gates for the web tools.
- Approval matrix — AUTO: `read`, `glob`, `grep`, `webfetch`, `websearch`, `skill`,
  `question` (the dialog is the gate), `ask_llm`, `get_subagent_logs`, `list_tools`;
  ASK: `edit`, `write`, `shell`, `execute`, `subagent`.
- UI fallout: Tools settings panel shows 15 standard + 31 KeY-specific rows;
  `llm-settings-tools.png` regenerates; tool console needs no change (schema-driven).

## Rollout (commit staging, each spotless-clean)

1. Renames/reshapes of existing standard tools + constants + interception + tests
   (drop `file_info`).
2. New file tools `write` and `grep` + tests.
3. Web & scripting: jsoup dependency, `webfetch`/`websearch`, `execute` (JShell + facade +
   outside-lock), settings, categories, tests.
4. Docs (`key-agent-doc.md`, `docs/LLM-Client-Extended.md`, `docs/mcp-server.md`,
   `docs/subagents.md`, `docs/mcp-server-ui-testing.md`), PR description, key-docs sync +
   screenshot regen.

## Testing

- New unit tests: glob matching/limits, grep modes/limits, write (parent dirs, sandbox),
  HTML→Markdown converter (fixture), websearch parser (fixture), execute (facade,
  timeout, output bound, toggle), multi-question parsing, outside-lock dispatch.
- Updated: file edit semantics (differs-check), shell parameters, interception tests,
  metadata/name-pinning tests.
- Per commit: `spotlessCheck`, nullness compile, module test suite.

## Deviations from this design (as built)

1. **`shell.background?` dropped.** OpenCode's `background` parameter has no KeY-side
   counterpart: KeY backgrounding is a chat-panel/agent-loop feature (the user moves a running
   call into a background job; see `key-agent-doc.md` section 7.5), not a tool argument. The
   backgroundable metadata flag covers it; the omission is visible in `shell`'s description.
2. **Facade binding via a per-execution registry key, not a ThreadLocal.** Probing showed the
   local JShell engine evaluates snippets on its own thread while `clientCodeEnter` runs on the
   caller thread — a ThreadLocal binding set before `eval` never reaches the snippet. The
   preamble is therefore `var tools = org.key_project.key.llm.ToolFacade.byKey("<uuid>")` with
   the facade published under a fresh UUID per call (`ToolFacade.register/unregister`).
3. **Multi-statement snippets are split statement by statement** (via
   `SourceCodeAnalysis.analyzeCompletion`, the JShell REPL's own splitting): a single `eval` of
   `"int x = 21; x*2+1"` yields only one event and silently loses the trailing expression.
4. **The safety gate is a best-effort blocklist, not confinement.** It rejects the obvious
   escape hatches (`ProcessBuilder`, `System.exit`, reflection, raw file/network I/O) by token
   match on the source — trivially bypassable in unrestricted-ish ways; the ASK approval per
   call is the security boundary, as the tool description and docs state.
5. **`execute` reports expression values only** (method-call expressions and the temporary
   `$`-named variables JShell creates for bare expressions); the initializers of user-declared
   variables are not echoed.
6. **The `question` schema is looser than the spec's mapping row** (header/options optional, no
   30-char/1–5-word label enforcement): the runtime parsing stays tolerant (a bare string is a
   valid question), the schema does not over-promise; recorded after the final review.
7. **The `shell` `timeout` default differs from OpenCode's 120000 ms**: the effective default
   is the configured shell-timeout setting (30 s) because the parameter is capped by it; the
   tool description states the effective default (recorded after the final review).

## Final review (2026-11-11, fresh reviewer over f07a1e399a..bfd85fcd12)

Verdict: "No — one Critical must be fixed first": 1 Critical, 6 Important, 8 Minor.
Critical + Important were fixed in one TDD pass (`f51c63350d`), RED→GREEN each:
execute approval on the loop path (intercept consults the approval policy,
`decideApproval` re-dispatches through the JShell path), bounded shell output read,
bounded webfetch body (Content-Length pre-check + streaming drain), subagent schema in
the docs, webfetch/shell description honesty, test gaps (approval pause/denial, outside-lock,
multi-question, skill `id`, copy constructor).

**Deferred minors** (each `Final: minor (deferred):`):

- JShell leak per timed-out snippet (the abandoned shell is stopped but not closed; safe for
  this engine per the reviewer's probe, one parked thread leaks) + cosmetic double
  `executor.shutdownNow()`.
- `toMarkdown`'s internal truncation check compares chars to bytes (dead code in production;
  the note comes from `cap()`), and the byte cut can split a UTF-8 sequence (harmless U+FFFD).
- `visible()`/`skipped()` filter dot/`build`-like segments against the absolute path: a jail
  under `~/.config/…` or a `build` segment filters everything in `glob`/`grep`
  (pre-existing in `FileAccess`, inherited; fix = relativize before the segment check).
- CRLF parity with OpenCode's `read`/`edit` (read emits platform separators; edit lacks the
  CRLF/typographic fallback).
- `write` bypasses `maxFileSizeKB` (which `read`/`edit` enforce; ASK-gated).
- Stale small docs: `SubagentRole` javadoc ("`role` argument", "`mode: parallel`"), the
  `tool-tour` skill lists `edit` under read-only, `glob`/`read` schemas don't mark `path`
  required, the 500-entry directory cap has no truncation note, the spec's "danger-styled"
  toggle is a plain checkbox.
- Deferred follow-up, **done 2026-11-11**: the approval pause and the approved (re-)dispatch
  are one shared pair of helpers (`AgentLoop.pauseForApproval` / `dispatchApproved`), applied
  to the ordinary path, `execute` and `subagent` — the pre-existing subagent approval gap is
  closed (the ask-approval the docs always promised now actually pauses).
- Approved tools are missing from the final `Done` activity list: `decideApproval` appends
  the tool result to the context but never to `activities` (pre-existing for every approved
  tool; the chat panel's per-call activity summary omits them).

**Declined-to-judge items, ruled by the executor:** PNG pixel content — accepted, the
regenerated screenshots were visually inspected (new tool rows in the Tools panel); jsoup
1.21.2/`implementation` scope — accepted; the spec's 11→15 arithmetic — accepted as spec
bookkeeping (the registry size is pinned by tests, not the spec); `ShellSafetyPolicy` regex
content — pre-existing, out of range; `KeYAgentTools --json` CLI — unchanged behavior; no
Gradle runs by the reviewer — the executor ran the module suite, `spotlessCheck` and the
nullness build green; `ToolConsoleDialog` flow — unchanged generic approval path, covered by
`ToolConsoleUiTest`.
