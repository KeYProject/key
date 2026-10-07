# KeY-Agent

The KeY-Agent is a chat-based assistant integrated into the KeY GUI that supports interactive
program verification and theorem proving with the help of a large language model. It can inspect
the current proof state, read the files of the current Java model, and run safe shell commands —
while keeping the user in control through per-call approval and question dialogs.

The module lives in `keyext.llm` (main classes `org.key_project.key.llm.*`). The chat window is
deliberately thin: all prompt assembly happens in `ExtendedPrompt`, an agent turn is driven by
`AgentLoop`, and the input markup is resolved by `PromptResolver`.

---

## 1. Getting started

1. Open the **KeY-Agent** panel (KeY GUI, menu *Proof → LLM → Open LLM prompt*, or Ctrl+K).
2. Open *Settings → LLM Settings* and configure a connection:
   - **API Base URL** — an OpenAI-compatible endpoint (default
     `https://ki-toolbox.scc.kit.edu/v1`).
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
│ [attach proof context] [Prompts]          [Clear history] [Stop]         │
├──────────────────────────────────────────────────────────────────────────┤
│ history of inputs / answers / errors / tool activity                    │
│  · right-click a message for actions (e.g. "into input")                │
├──────────────────────────────────────────────────────────────────────────┤
│ tabs: [Prompt] [Files]                                                   │
│  Prompt tab: multi-line input box                       "Ctrl+Enter to send" │
│  Files tab  : checkboxes to attach model files to the conversation    │
└──────────────────────────────────────────────────────────────────────────┘
```

- **Sending.** `Ctrl+Enter` sends the current input (there is no send button). `Shift+Enter` and
  plain Enter insert a line break.
- **Running a turn.** While a turn is running, the *Stop* button cancels it. Only one turn runs at
  a time.
- **Files.** The *Files* tab lists the files of the current Java model (bounded); ticking a file
  attaches it to the conversation. Attached files are reported by the `$selectedFiles` token.
- **Tool activity.** After a turn, the tool calls that were executed are summarized in the chat
  (can be turned off in the settings).

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
Java model directory.

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

The popup never steals the keyboard focus, so you can select an entry and keep typing.

### 4.5 Inline expansion (Ctrl+Space)

Pressing **Ctrl+Space** right after a fragment replaces the fragment with its *currently resolved*
content, so you can edit the actual value instead of the reference:

- `$seq` becomes the literal sequent text
- `@src/Main.java` becomes the embedded file content
- `/skills` becomes the current listing, `/prompt:name` the rendered template

Unknown `$tokens` and bare activation directives (`/skill:name`) are left untouched.

---

## 5. Skills

A **skill** is a named bundle of instructions that is appended to the system prompt while active,
optionally restricting the tool set:

```jsonc
// <key-config-dir>/llm/skills/<name>.json
{
  "name": "optics",
  "description": "focus on arithmetic overflow proofs",
  "instructions": "Pay special attention to integer overflow; ...",
  "allowedTools": ["list_files", "read_file", "get_proof_context"], // empty = no restriction
  "enabled": true
}
```

- Skills are managed in **Settings → LLM Settings → Skills**: a list of the stored skills, with
  `New`/`Edit`/`Delete` (editing happens in a dialog) and `Export...`/`Import...` to share the
  whole library as a JSON file (see [section 9](#9-settings-reference-settings--llm-settings)).
- If a skill restricts `allowedTools`, only those tools are offered to the model while the skill
  is active.
- The agent itself can activate a skill through the `use_skill` tool — this is **off by default**
  (setting *Agent may use skills*).

---

## 6. Prompts

A **prompt** is a named, reusable message template:

```jsonc
// <key-config-dir>/llm/prompts/<name>.json
{
  "name": "prove-method",
  "description": "prove the postcondition of the selected method",
  "template": "Prove the selected method. Collect $proof and $seq, ..."
}
```

Templates are inserted from the *Prompts* toolbar button or via `/prompt:name`; markup inside the
template is resolved like normal input. Prompts are managed in **Settings → LLM Settings →
Prompts**: a list of the stored prompts with `New`/`Edit`/`Delete` (editing happens in a dialog)
and `Export...`/`Import...` to share the whole library as a JSON file.

---

## 7. The agent loop and tools

A turn is driven by `AgentLoop`: the assembled request is sent to the model, tool calls in the
response are executed, the results are fed back, and the loop continues until a final answer, a
question, an approval request, an error, or the maximum number of tool rounds is reached
(`max rounds`, default 8).

The built-in tool set (`KeYAgentTools`):

| Tool                | Approval | Description                                                         |
|---------------------|----------|---------------------------------------------------------------------|
| `get_proof_context` | auto     | a text block describing the current proof state                     |
| `list_files`        | auto     | bounded listing of the files of the current Java model              |
| `read_file`         | auto     | read a text file of the model directory (respects size limits)      |
| `file_info`         | auto     | metadata (size, last modified, kind) of a file                      |
| `run_command`       | ask      | run a shell command in the model directory (blocklist + approval)   |
| `ask_user`          | auto     | ask the user a question; the turn pauses until it is answered       |
| `use_skill`         | auto     | activate a user-defined skill by name (only if enabled in settings) |
| `tryclose`          | auto     | apply the `tryclose` proof-script command (TryClose macro) to the current branch, all open goals, or a goal by index |
| `auto`              | auto     | apply KeY's automatic proof strategy ('Auto' button) with an arbitrary step limit |

### 7.1 Questions

The agent can ask you a question (e.g. about a case split or a design decision), which pauses the
turn until you answer. Turn this off with *Allow the agent to ask questions*.

### 7.2 Approval and the safety model

- File access tools are **read-only**, restricted to the current Java model directory, and run
  without approval.
- `tryclose` and `auto` are the first tools that **modify the current proof** (they run the
  corresponding proof-script commands, i.e. the same actions as *Apply Script* / the *Auto*
  button). They are approved by default so the agent can actually prove, but you can move them
  to *with approval* in the Tools panel if you want to review each invocation.
- `run_command` *always* requires per-call approval, and commands matching the configured
  **blocklist** (e.g. `rm -rf /`, `sudo`, `chmod -R` on system directories, `curl … | sh`) are
  refused regardless of approval.
- Each tool call's approval/disabled behavior can be customized in the *Tools* panel
  (**Settings → LLM Settings → Tools**): tools can be disabled entirely, or moved to *with
  approval* / *without approval (always)*.
- The tools exposed to the model never include the ones you disabled.

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

The main *LLM Settings* panel holds the sections below; **Tools**, **Prompts** and **Skills**
are edited in their own panels.

### Connection
| Setting | Default |
|---|---|
| API Base URL | `https://ki-toolbox.scc.kit.edu/v1` |
| Auth Token | — |
| Default model | `azure.gpt-4.1-mini` |
| Available models | editable list; `Fetch Models` pulls it from the endpoint |

### Agent behavior
| Setting | Default |
|---|---|
| System prompt | built-in KeY-Agent prompt |
| Allow the agent to ask questions | `true` |
| Max tool rounds | `8` |
| Send temperature | `false` (`temperature` 0.2) |
| Send max output tokens | `false` (`4096`) |
| Agent may use skills (`use_skill`) | `false` |

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
One row per tool with three checkboxes: **Disabled**, **With approval**, **Without approval
(always)**. Read tools are auto-approved by default; `run_command` asks by default.

### User interface
Auto-scroll output (`true`) and show tool activity (`true`).

### Prompts / Skills (sub-panels)
Editors for the user libraries described in [section 5](#5-skills) and [section 6](#6-prompts):
the entries are shown as a selectable list (name + description), `New`/`Edit` (or double click)
open a dialog with the full form and `Delete` removes the selected entry. `Export...` saves the
whole library as a JSON file, `Import...` merges one back in (new entries are added; entries with
an existing name are only overwritten after you confirm, otherwise they are kept). Changes are
saved immediately.

---

## 10. Storage

User-defined prompts and skills are stored as JSON files in the KeY configuration directory
(`llm/prompts` and `llm/skills`), e.g. `~/.key/llm/prompts/<name>.json` when no custom config
directory is set. The chat history and selected models are part of the proof session and are not
persisted as files.

---

## 11. Architecture (code pointers)

| Concern             | Class                                              |
|---------------------|----------------------------------------------------|
| Chat panel (thin UI)| `org.key_project.key.llm.LlmPrompt`                |
| Agent turn driver   | `org.key_project.key.llm.AgentLoop`                |
| Request assembly    | `org.key_project.key.llm.ExtendedPrompt`           |
| Input markup        | `org.key_project.key.llm.PromptResolver`           |
| Autocompletion      | `org.key_project.key.llm.AutocompleteInput` + `AutocompleteProviders` |
| Built-in tools      | `org.key_project.key.llm.mcp.KeYAgentTools`        |
| Shell safety        | `org.key_project.key.llm.ShellSafetyPolicy`        |
| Proof context       | `org.key_project.key.llm.ProofContextCollector`    |
| Settings            | `org.key_project.key.llm.LlmSettings` / `LlmSettingsUI` / `LlmToolsPanel` |
| Skill library       | `org.key_project.key.llm.SkillLibrary` + `Skill`   |
| Prompt library      | `org.key_project.key.llm.PromptLibrary` + `Prompt` |
