# Sub-agents in the KeY-Agent

Status: **Phases 1–3 implemented** (sequential delegation, parallel fan-out, observability).

## Idea

A sub-agent is a *delegated, bounded tool loop*: the delegating agent calls
`spawn_subagent`, the agent loop (instead of dispatching it like a normal tool) runs a nested
loop with a fresh message thread, a role-specific system prompt and a restricted tool whitelist,
and returns the child's final answer as the tool result. This is **method 1 (recursive
delegation)** from the design discussion: a dedicated child loop rather than prompt-only
emulation, so the child gets real tool access and produces real results the parent can parse.

## Roles

A role (`SubagentRole`) couples:

| field            | meaning                                                        |
|------------------|----------------------------------------------------------------|
| `name`           | id used as the `role` argument of `spawn_subagent`             |
| `description`    | shown to the delegating agent                                 |
| `systemPrompt`   | instructions prepended to the child's system prompt           |
| `allowedTools`   | tool whitelist (empty = inherit all enabled tools)            |
| `model`          | optional model override (empty = parent's model)              |
| `maxTurns`       | per-child tool-round budget (0 = global `maxSubagentTurns`)   |
| `parallelAllowed`| whether `mode: parallel` may be used                          |

Roles are contributed by `SubagentRoleProvider`s via `ServiceLoader`
(`META-INF/services/org.key_project.key.llm.subagents.SubagentRoleProvider`) — the same pattern
as `AgentToolProvider`, so plugins can add roles without touching core classes.
`SubagentRegistry` aggregates them.

Built-in roles:

| role            | tools                                                              | parallel |
|-----------------|--------------------------------------------------------------------|----------|
| `goal-solver`   | `get_proof_context`, `list_proofs`, `tryclose`, `auto`, `list_taclets` | yes   |
| `file-explorer` | `list_files`, `read_file`, `file_info`                             | yes      |
| `rule-designer` | taclet inspection + `add_taclet`/`remove_taclet`                   | no       |

## Execution

`AgentLoop.processBatch` intercepts `spawn_subagent` (like `ask_user`/`use_skill`) and calls
`SubagentRunner.run(...)`, which:

1. resolves the role and the `mode` argument (`sequential` or `parallel`),
2. applies the settings gate (`subagentsEnabled`) and the depth guard (`maxSubagentDepth`,
   thread-local so nested delegations are bounded),
3. runs the child loop: fresh `LlmContext`, system prompt + task, advertised tools =
   whitelist ∩ enabled tools of the parent session,
4. dispatches the child's tool calls through the parent's `BuiltInMCPClient` — a nested
   `spawn_subagent` is intercepted again (depth-guarded recursion),
5. returns `[sub-agent '<role>' finished after N round(s), called: ...]` + the child's final
   answer as the tool result text.

### Parallel fan-out

`mode: parallel` runs the `tasks` array (list of independent task strings) concurrently, one
worker thread per task on a shared fixed-size pool. Constraints:

- only roles with `parallelAllowed` accept it, and at least one task is required,
- the pool size is `min(tasks, maxParallelSubagents)` — extra tasks queue and run as workers
  finish,
- **tool dispatch is serialized** through a global lock: KeY `Proof` objects and the GUI
  mediator are not thread-safe, so the parallelism is in the LLM round-trips (each worker owns
  its own message thread and a fresh HTTP call) while every mutation/queries on the proof are
  mutually exclusive. Nested `spawn_subagent` calls happen *outside* that lock, so parallel
  nesting cannot deadlock,
- the merged result is one tool message: a run header, then `(1) …`, `(2) …` per task (a task
  that failed/interrupted is reported as such, the rest still run to completion),
- the depth guard applies per worker thread (a parallel worker is at depth `parentDepth + 1`),
  so a broadcaster can hand out tasks but filling sub-sub-agents is still bounded.

### Safety model

- The `spawn_subagent` call itself defaults to **ask-approval** (the child runs autonomously,
  so the approval happens before it starts; the child never pauses for approval).
- The child only ever sees/calls whitelisted tools, and the global Tools-panel disabled set
  still applies.
- Rounds and nesting depth are hard-bounded; parent cancellation (`AgentLoop.cancel()`) is
  propagated via a `BooleanSupplier`.
- The child system prompt asks for a final answer starting with
  `KEY_AGENT_RESULT {"summary": "..."}` so outcomes are machine-readable for the delegating
  agent.

### Result contract

The tool result is a plain text message: a short run header plus the child's final answer.
Structured parsing of `KEY_AGENT_RESULT {json}` is left to the delegating agent (the marker is
kept verbatim); a dedicated structured field in the result is a later refinement.

## Settings (`LlmSettings`)

| key                    | default | meaning                         |
|------------------------|---------|---------------------------------|
| `subagentsEnabled`     | `false` | `spawn_subagent` allowed at all |
| `maxSubagentTurns`     | `8`     | global per-delegation round budget |
| `maxSubagentDepth`     | `2`     | maximum nesting depth (1 = children may not spawn children) |
| `maxParallelSubagents` | `4`     | concurrent workers in one parallel run (pool size) |

## Observability

Every finished delegation is recorded in the per-session `SubagentLog` (bounded, thread-safe,
sequence-numbered so parallel workers can append concurrently):

- **`get_subagent_logs`** (read-only, auto-approval) renders the recorded runs for the model:
  role, mode, timing, and per task the status (`OK` / `stopped (round limit)` / `cancelled` /
  `failed`), the number of tool rounds and the tools that were called. Optional `limit` and
  `role` parameters.
- **Chat panel:** the tool-activity summary shows the `spawn_subagent` row with one indented
  child line per delegated task (role + task, tooltip = mode + outcome), honoring the existing
  *Show tool activity* setting. *Clear history* clears the sub-agent log together with the
  conversation.
- **Status tracking:** hard terminations are recorded distinctly — `STOPPED` (round budget),
  `CANCELLED` (turn cancelled), `FAILED` (completion/parse error) — so `get_subagent_logs`
  reflects why a sub-agent did not deliver an answer.

## Files

| file | role |
|------|------|
| `org.key_project.key.llm.SubagentRunner` | the child loop + guards |
| `org.key_project.key.llm.mcp.tools.SubagentTools` | the `spawn_subagent` tool schema (intercepted by `AgentLoop`) |
| `org.key_project.key.llm.subagents.SubagentRole` / `SubagentRoleProvider` / `SubagentRegistry` / `BuiltInSubagentRoles` | role model + service loading |
