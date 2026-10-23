/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.util.List;

import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.AgentToolProvider;
import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.Tool;
import org.key_project.key.llm.subagents.SubagentRegistry;

/**
 * The {@code spawn_subagent} tool. Its schema is advertised to the model, but the call itself is
 * intercepted by the agent loop ({@code AgentLoop} runs the sub-agent) - like {@code ask_user}
 * and {@code use_skill}, a direct call only produces an explanatory placeholder. Requires user
 * approval by default, because a sub-agent works autonomously on its whole tool round.
 *
 * @author Alexander Weigl
 */
public final class SubagentTools implements AgentToolProvider {

    @Override
    public List<AgentTool> get() {
        var roleNames = SubagentRegistry.INSTANCE.roleNames();
        return List.of(AgentTool.tool(KeYAgentTools.TOOL_SPAWN_SUBAGENT,
            "Delegates a task to a sub-agent with a dedicated role. The sub-agent runs its own"
                + " bounded tool loop with a role-specific system prompt and a restricted tool"
                + " whitelist, and returns a summary. Available roles: "
                + String.join(", ", roleNames) + ". Use \"mode\": \"sequential\" with a \"task\""
                + " for one sub-agent, or \"mode\": \"parallel\" with a \"tasks\" array of"
                + " independent tasks (run concurrently, capped by the max-parallel-sub-agents"
                + " setting; only roles that allow parallel execution accept it). Enabled only"
                + " when the 'agent may spawn sub-agents' setting is on.",
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
            args -> "[spawn_subagent is handled by the agent loop; it cannot be called"
                + " directly]"));
    }
}
