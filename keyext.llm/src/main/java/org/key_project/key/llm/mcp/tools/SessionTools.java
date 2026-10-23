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

/**
 * The interactive session tools {@code ask_user} and {@code use_skill}. Their schemas are
 * advertised to the model, but the calls themselves are intercepted by the agent loop
 * ({@code AgentLoop} handles them specially and they never reach the client), so direct calls
 * only produce an explanatory placeholder text.
 *
 * @author Alexander Weigl
 */
public final class SessionTools implements AgentToolProvider {
    @Override
    public List<AgentTool> get() {
        return List.of(
            AgentTool.tool(KeYAgentTools.TOOL_ASK_USER,
                "Asks the user a question. Use this whenever a case split, an assumption or a"
                    + " design decision is ambiguous. The user's answer is returned verbatim.",
                AgentTool.schema("question",
                    JsonSchema.builder().withType("string").withDescription("the question text")
                            .build(),
                    "options",
                    JsonSchema.builder().withType("array")
                            .withDescription("optional answer options")
                            .withItems(JsonSchema.builder().withType("string").build()).build()),
                args -> "[ask_user is interactive and handled by the agent loop; it cannot be"
                    + " called directly]"),
            AgentTool.tool(KeYAgentTools.TOOL_USE_SKILL,
                "Activates a user-defined skill by name. Skills add focused instructions to the"
                    + " system prompt of this and subsequent turns. Enabled only when the 'agent"
                    + " can use skills' setting is on.",
                AgentTool.schema("name",
                    JsonSchema.builder().withType("string")
                            .withDescription("the name of the skill to activate").build()),
                args -> "[use_skill is handled by the agent loop; it cannot be called directly]"));
    }
}
