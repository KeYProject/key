/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.util.List;

import org.key_project.key.llm.LlmUtils;
import org.key_project.key.llm.SubagentLog;
import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.AgentToolProvider;
import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.ProofSelector;
import org.key_project.key.llm.mcp.Tool;
import org.key_project.key.llm.mcp.ToolCategory;
import org.key_project.key.llm.subagents.SubagentRegistry;

/**
 * The {@code spawn_subagent} tool, the self-consultation tool {@code ask_llm} and the
 * observability counterpart {@code get_subagent_logs}. The {@code spawn_subagent} schema is
 * advertised to the model, but the call itself is intercepted by the agent loop ({@code AgentLoop}
 * runs the sub-agent) - like {@code ask_user} and {@code use_skill}, a direct call only produces
 * an explanatory placeholder. It requires user approval by default, because a sub-agent works
 * autonomously on its whole tool round. {@code ask_llm} is likewise intercepted by the agent loop
 * (and by the sub-agent child loops) so the nested one-shot completion never occupies the global
 * dispatch lock; it is AUTO-approved because it only sends a text prompt and never touches the
 * proof or any side-effectful tool. {@code get_subagent_logs} is a plain read-only tool that
 * renders the session's recorded runs.
 *
 * @author Alexander Weigl
 */
public final class SubagentTools implements AgentToolProvider {

    @Override
    public List<AgentTool> get() {
        var roleNames = SubagentRegistry.INSTANCE.roleNames();
        return List.of(AgentTool.tool(KeYAgentTools.TOOL_SPAWN_SUBAGENT, ToolCategory.SUBAGENTS,
            "Delegates a task to a sub-agent with a dedicated role. The sub-agent runs its own"
                + " bounded tool loop with a role-specific system prompt and a restricted tool"
                + " whitelist, and returns a summary. Available roles: "
                + String.join(", ", roleNames) + ". Use \"mode\": \"sequential\" with a \"task\""
                + " for one sub-agent, or \"mode\": \"parallel\" with a \"tasks\" array of"
                + " independent tasks (run concurrently, capped by the max-parallel-sub-agents"
                + " setting; only roles that allow parallel execution accept it). Delegation may"
                + " take a while; this tool can run in the background, so you can keep asking"
                + " questions while it works. Enabled only when the 'agent may spawn sub-agents'"
                + " setting is on.",
            Tool.ApprovalRequirement.ASK,
            AgentTool.schema("role",
                JsonSchema.builder().withType("string").withDescription("the sub-agent role")
                        .withEnum(roleNames).build(),
                "task",
                JsonSchema.builder().withType("string").withDescription(
                    "the precise task the sub-agent should solve on its own (sequential"
                        + " mode)").build(),
                "tasks",
                JsonSchema.builder().withType("array")
                        .withDescription("independent tasks solved concurrently (parallel mode)")
                        .withItems(JsonSchema.builder().withType("string").build()).build(),
                "mode",
                JsonSchema.builder().withType("string")
                        .withDescription("execution mode ('sequential' or 'parallel')")
                        .withEnum(List.of("sequential", "parallel")).build(),
                "model",
                JsonSchema.builder().withType("string")
                        .withDescription("optional model override for the sub-agent").build()),
            true,
            args -> "[spawn_subagent is handled by the agent loop; it cannot be called"
                + " directly]"),
            AgentTool.tool(KeYAgentTools.TOOL_ASK_LLM, ToolCategory.SUBAGENTS,
                "Sends the given \"prompt\" to a FRESH instance of the configured LLM - a"
                    + " one-shot completion with a clean, empty context (no conversation history,"
                    + " no tools) - and delivers the reply back to the caller. Use it to think"
                    + " about your own reasoning: review a draft plan, play devil's advocate,"
                    + " summarize noisy tool output through fresh eyes, or get a second opinion"
                    + " from another model via the optional \"model\" override. The reply is"
                    + " plain text; it does not see the current proof or conversation. Enabled"
                    + " only when the 'agent may consult the LLM' setting is on.",
                JsonSchema.builder().withType("object")
                        .addProperty("prompt",
                            JsonSchema.builder().withType("string").withDescription(
                                "the prompt for the fresh model context; must be self-contained, since"
                                    + " the fresh context has no conversation history")
                                    .build())
                        .addProperty("system",
                            JsonSchema.builder().withType("string").withDescription(
                                "optional system prompt of the fresh context (default: none - the"
                                    + " model sees only the prompt)").build())
                        .addProperty("model",
                            JsonSchema.builder().withType("string").withDescription(
                                "optional model override (default: the session's model)").build())
                        .addRequired("prompt")
                        .build(),
                true,
                args -> "[ask_llm is handled by the agent loop; it cannot be called directly]"),
            AgentTool.tool(KeYAgentTools.TOOL_GET_SUBAGENT_LOGS, ToolCategory.SUBAGENTS,
                "Lists the sub-agent runs recorded for the current session (newest first,"
                    + " empty until spawn_subagent has been used): role, mode, timing, and per"
                    + " task the status, the number of tool rounds and the tools that were"
                    + " called. Optional \"role\" filter and \"limit\".",
                AgentTool.schema("limit",
                    JsonSchema.builder().withType("integer")
                            .withDescription("maximum number of runs to list (default 10)")
                            .build(),
                    "role",
                    JsonSchema.builder().withType("string")
                            .withDescription("only list runs of this sub-agent role").build()),
                args -> {
                    var proof = ProofSelector.selectedProof();
                    var log = LlmUtils.getSession(proof).getSubagentLog();
                    Integer limitArg = AgentTool.intArg(args, "limit");
                    int limit = limitArg == null ? 10 : Math.max(1, Math.min(limitArg, 100));
                    return renderSubagentLog(log, limit, AgentTool.stringArg(args, "role"));
                }));
    }

    /** Renders the session's sub-agent log for the model (newest first). */
    public static String renderSubagentLog(SubagentLog log, int limit, String role) {
        var runs = log.snapshot(limit);
        if (runs.isEmpty()) {
            return "No sub-agent runs recorded for this session.";
        }
        var sb = new StringBuilder("Sub-agent runs for this session (newest first):\n");
        int shown = 0;
        for (var run : runs) {
            if (role != null && !role.isBlank() && !role.equals(run.role())) {
                continue;
            }
            shown++;
            sb.append("#").append(run.seq()).append(' ').append(run.role())
                    .append(" (mode: ").append(run.mode()).append(") · ")
                    .append(run.tasks().size()).append(" task(s) · ")
                    .append(time(run.startedAt())).append(" · ")
                    .append(duration(run.durationMs())).append('\n');
            for (var task : run.tasks()) {
                sb.append("  task \"").append(clip(task.task(), 80)).append("\" → ")
                        .append(task.status().label()).append(" after ")
                        .append(task.rounds()).append(" round(s)");
                if (!task.tools().isEmpty()) {
                    sb.append("; called: ").append(String.join(", ", task.tools()));
                }
                sb.append('\n');
            }
        }
        if (shown == 0) {
            return "No sub-agent runs recorded for this session with role '" + role + "'.";
        }
        return sb.toString().stripTrailing();
    }

    private static String duration(long ms) {
        if (ms < 1000) {
            return ms + " ms";
        }
        return String.format(java.util.Locale.ROOT, "%.1f s", ms / 1000.0);
    }

    private static String time(long epochMillis) {
        return java.time.Instant.ofEpochMilli(epochMillis).toString().replace('T', ' ').substring(0,
            19);
    }

    static String clip(String s, int max) {
        if (s == null) {
            return "";
        }
        return s.length() <= max ? s : s.substring(0, max) + "…";
    }
}
