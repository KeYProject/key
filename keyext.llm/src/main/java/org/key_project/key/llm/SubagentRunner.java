/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.function.BooleanSupplier;

import org.key_project.key.llm.LlmContext.LlmMessage;
import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.subagents.SubagentRegistry;
import org.key_project.key.llm.subagents.SubagentRole;

/**
 * Executes one sub-agent delegation: a nested, bounded tool-calling loop with a fresh message
 * thread, a role's system prompt and tool whitelist, and the parent's chat-completion client
 * (endpoint/auth come from the parent {@link LlmSession}). Invoked synchronously by
 * {@link AgentLoop} when it intercepts the {@code spawn_subagent} tool call.
 * <p>
 * Two {@code mode}s:
 * <ul>
 * <li>{@code sequential} - one sub-agent solves one {@code task} (the default),</li>
 * <li>{@code parallel} - the {@code tasks} array is solved concurrently, one worker thread per
 * task on a shared pool, capped by the {@code maxParallelSubagents} setting. Only roles with
 * {@code parallelAllowed} accept it. The win is parallel LLM round-trips: tool <em>dispatch</em>
 * is serialized through a global lock, because KeY proofs and the GUI mediator are not
 * thread-safe.</li>
 * </ul>
 * Safety:
 * <ul>
 * <li>only the tools of the role's whitelist are advertised and may be dispatched (the parent's
 * session client still applies the global disabled set),</li>
 * <li>the child never asks the user and never pauses for approvals (the {@code spawn_subagent}
 * call itself was the approval point),</li>
 * <li>nesting is bounded by a thread-local depth counter ({@code maxSubagentDepth} setting),
 * so a sub-agent cannot spawn unbounded chains of sub-agents,</li>
 * <li>tool rounds are bounded by the role's budget, cancellations are propagated from the
 * parent loop.</li>
 * </ul>
 * The result is a single text message for the delegating agent that summarizes the run and
 * contains the child's final answer(s), so the parent can parse the {@code KEY_AGENT_RESULT}
 * markers if the child complied with the system prompt.
 *
 * @author Alexander Weigl
 */
final class SubagentRunner {

    private static final ThreadLocal<Integer> DEPTH = ThreadLocal.withInitial(() -> 0);

    /**
     * Serializes every tool dispatch, so concurrent parallel sub-agents never race on the shared
     * proof state or the GUI mediator. Nested {@code spawn_subagent} calls happen outside the
     * lock, so parallel nesting cannot deadlock.
     */
    private static final Object DISPATCH_LOCK = new Object();

    private SubagentRunner() {
    }

    /**
     * Runs the {@code spawn_subagent} tool call: validates the arguments, applies the settings
     * and depth guards and executes the child loop(s). Returns the tool result text to be
     * inserted into the parent's thread.
     */
    static String run(LlmSession parent, ChatCompletionsClient completions, String arguments,
            BooleanSupplier cancelled) {
        var args = AgentTool.parseArgs(arguments);
        var roleName = AgentTool.stringArg(args, "role");
        var role = roleName == null ? null : SubagentRegistry.INSTANCE.get(roleName);
        if (role == null) {
            return "[spawn_subagent: unknown role '" + roleName + "' (known roles: "
                + String.join(", ", SubagentRegistry.INSTANCE.roleNames()) + ")]";
        }
        var mode = AgentTool.stringArg(args, "mode");
        if ("parallel".equalsIgnoreCase(mode)) {
            return runParallel(parent, completions, role, args, cancelled);
        }
        return runSequential(parent, completions, role, args, cancelled);
    }

    // ------------------------------------------------------------------ sequential delegation

    private static String runSequential(LlmSession parent, ChatCompletionsClient completions,
            SubagentRole role, Map<String, Object> args, BooleanSupplier cancelled) {
        var task = AgentTool.stringArg(args, "task");
        if (task == null || task.isBlank()) {
            return "[spawn_subagent: the 'task' parameter must not be empty]";
        }
        int depth = DEPTH.get();
        int maxDepth = Math.max(1, LlmSettings.INSTANCE.getMaxSubagentDepth());
        if (depth >= maxDepth) {
            return "[spawn_subagent: maximum nesting depth (" + maxDepth + ") reached]";
        }
        DEPTH.set(depth + 1);
        try {
            return runOne(parent, completions, role, task, cancelled);
        } finally {
            DEPTH.set(depth);
        }
    }

    // ------------------------------------------------------------------ parallel fan-out

    private static String runParallel(LlmSession parent, ChatCompletionsClient completions,
            SubagentRole role, Map<String, Object> args, BooleanSupplier cancelled) {
        if (!role.parallelAllowed()) {
            return "[spawn_subagent: role '" + role.name() + "' does not allow parallel execution]";
        }
        var tasks = stringListArg(args, "tasks");
        if (tasks.isEmpty()) {
            return "[spawn_subagent: parallel mode requires a non-empty \"tasks\" array]";
        }
        int depth = DEPTH.get();
        int maxDepth = Math.max(1, LlmSettings.INSTANCE.getMaxSubagentDepth());
        if (depth >= maxDepth) {
            return "[spawn_subagent: maximum nesting depth (" + maxDepth + ") reached]";
        }
        int poolSize =
            Math.min(tasks.size(), Math.max(1, LlmSettings.INSTANCE.getMaxParallelSubagents()));
        var pool = Executors.newFixedThreadPool(poolSize);
        try {
            var futures = new ArrayList<Future<String>>();
            for (int i = 0; i < tasks.size(); i++) {
                var task = tasks.get(i);
                futures.add(pool.submit(() -> {
                    DEPTH.set(depth + 1);
                    try {
                        return runOne(parent, completions, role, task, cancelled);
                    } finally {
                        DEPTH.set(depth);
                    }
                }));
            }
            var sb = new StringBuilder();
            sb.append("[parallel run of ").append(tasks.size()).append(" sub-agents")
                    .append(" (role '").append(role.name()).append("')]").append('\n');
            for (int i = 0; i < futures.size(); i++) {
                if (i > 0) {
                    sb.append("\n--------\n");
                }
                try {
                    sb.append('(').append(i + 1).append(") ").append(futures.get(i).get());
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                    sb.append('(').append(i + 1).append(") [sub-agent interrupted]");
                } catch (ExecutionException e) {
                    var cause = e.getCause();
                    sb.append('(').append(i + 1).append(") [sub-agent failed: ")
                            .append(cause == null || cause.getMessage() == null ? "unknown error"
                                    : cause.getMessage())
                            .append(']');
                }
            }
            if (cancelled.getAsBoolean()) {
                sb.append('\n').append("(Parallel run stopped: the turn was cancelled.)");
            }
            return sb.toString();
        } finally {
            pool.shutdownNow();
        }
    }

    private static List<String> stringListArg(Map<String, Object> args, String key) {
        Object v = args.get(key);
        if (v instanceof List<?> list) {
            var result = new ArrayList<String>();
            for (Object item : list) {
                if (item != null) {
                    result.add(String.valueOf(item));
                }
            }
            return result;
        }
        return List.of();
    }

    // ------------------------------------------------------------------ the child loop

    private static String runOne(LlmSession parent, ChatCompletionsClient completions,
            SubagentRole role, String task, BooleanSupplier cancelled) {
        var tools = advertiseTools(parent, role);
        var model = role.model() != null && !role.model().isBlank() ? role.model()
                : parent.getModel();
        int maxTurns = role.maxTurns() > 0 ? role.maxTurns()
                : Math.max(1, LlmSettings.INSTANCE.getMaxSubagentTurns());

        var thread = new ArrayList<Map<String, Object>>();
        thread.add(Map.of("role", "system", "content", systemPrompt(role, maxTurns)));
        thread.add(Map.of("role", "user", "content", task));

        var called = new ArrayList<String>();
        int rounds = 0;
        while (true) {
            if (cancelled.getAsBoolean() || Thread.currentThread().isInterrupted()) {
                return "[sub-agent '" + role.name() + "' cancelled]";
            }
            if (rounds >= maxTurns) {
                return "[sub-agent '" + role.name() + "' stopped: reached its tool-round limit ("
                    + maxTurns + ") without a final answer]";
            }

            final Map<String, Object> response;
            try {
                response = completions.complete(parent,
                    new AgentRequest(model, List.copyOf(thread), tools, null, null, maxTurns));
            } catch (Exception e) {
                return "[sub-agent '" + role.name() + "' failed: " + e.getMessage() + "]";
            }

            final Map<?, ?> message;
            try {
                message = AgentLoop.extractMessage(response);
            } catch (Exception e) {
                return "[sub-agent '" + role.name() + "' failed: " + e.getMessage() + "]";
            }
            var toolCalls = AgentLoop.asList(message.get("tool_calls"));
            String content = message.get("content") == null ? ""
                    : String.valueOf(message.get("content"));

            if (toolCalls == null || toolCalls.isEmpty()) {
                var header = "[sub-agent '" + role.name() + "' finished after " + rounds
                    + " tool round(s)";
                if (!called.isEmpty()) {
                    header += ", called: " + String.join(", ", called);
                }
                header += "]";
                if (content.isBlank()) {
                    return header;
                }
                return header + "\n\n" + content.stripTrailing();
            }

            rounds++;
            thread.add(LlmMessage.assistant(content, AgentLoop.casts(toolCalls)).toOpenAiMap());
            for (var call : AgentLoop.casts(toolCalls)) {
                var id = String.valueOf(call.get("id"));
                Object func = call.get("function");
                var function = func instanceof Map<?, ?> f ? f : Map.of();
                var name = String.valueOf(function.get("name"));
                var callArguments = function.get("arguments") == null ? "{}"
                        : String.valueOf(function.get("arguments"));

                if (!allowedBy(role, name, parent)) {
                    thread.add(LlmMessage.tool(id, "[Tool '" + name + "' is not in the whitelist"
                        + " of role '" + role.name() + "']").toOpenAiMap());
                    continue;
                }
                called.add(name);
                // a sub-agent may delegate further (depth-guarded), exactly like the parent loop;
                // must run outside the dispatch lock, otherwise nested parallel runs deadlock
                if (KeYAgentTools.TOOL_SPAWN_SUBAGENT.equals(name)) {
                    if (!LlmSettings.INSTANCE.getSubagentsEnabled()) {
                        thread.add(LlmMessage.tool(id,
                            "[Spawning sub-agents is disabled in the settings]").toOpenAiMap());
                        continue;
                    }
                    var outcome = run(parent, completions, callArguments, cancelled);
                    thread.add(LlmMessage.tool(id, outcome).toOpenAiMap());
                    continue;
                }
                synchronized (DISPATCH_LOCK) {
                    try {
                        var result = parent.getMcpClient().callTool(name, callArguments);
                        thread.add(LlmMessage.tool(id, AgentLoop.stringify(result)).toOpenAiMap());
                    } catch (Exception e) {
                        thread.add(LlmMessage.tool(id,
                            "Error calling " + name + ": " + e.getMessage()).toOpenAiMap());
                    }
                }
            }
        }
    }

    /** The enabled tools of the parent session, restricted to the role's whitelist. */
    private static List<Map<String, Object>> advertiseTools(LlmSession parent, SubagentRole role) {
        var whitelist = role.allowedTools();
        return parent.getMcpClient().getTools().stream()
                .filter(t -> whitelist.isEmpty() || whitelist.contains(t.function().name()))
                .map(t -> t.toMap())
                .toList();
    }

    /**
     * Whether the child may dispatch the given tool: in the whitelist and not globally disabled.
     */
    private static boolean allowedBy(SubagentRole role, String name, LlmSession parent) {
        if (!role.allowedTools().isEmpty() && !role.allowedTools().contains(name)) {
            return false;
        }
        return !parent.getMcpClient().isDisabled(name);
    }

    private static String systemPrompt(SubagentRole role, int maxTurns) {
        var prompt = "You are the sub-agent '%s' of the KeY-Agent.\n%s\n\n"
            + "Be concise. You have at most %d tool rounds and must not ask the user anything. "
            + "When you are done, reply with only your final answer and start it with the line:\n"
            + "KEY_AGENT_RESULT {\"summary\": \"...\"}\n"
            + "Keep the JSON part on one line so the delegating agent can parse it.";
        return prompt.formatted(role.name(), role.systemPrompt(), maxTurns);
    }
}
