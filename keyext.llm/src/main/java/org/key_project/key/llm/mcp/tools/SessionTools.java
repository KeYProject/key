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
import org.key_project.key.llm.mcp.ToolCategory;

/**
 * The interactive session tools {@code question} and {@code skill}, following OpenCode's
 * parameter shapes. Their schemas are advertised to the model, but the calls themselves are
 * intercepted by the agent loop ({@code AgentLoop} handles them specially and they never reach
 * the client), so direct calls only produce an explanatory placeholder text.
 *
 * @author Alexander Weigl
 */
public final class SessionTools implements AgentToolProvider {
    @Override
    public List<AgentTool> get() {
        return List.of(
            AgentTool.tool(KeYAgentTools.TOOL_QUESTION, ToolCategory.INTERACTION,
                "Asks the user one or more questions. Use this whenever a case split, an"
                    + " assumption or a design decision is ambiguous. Each question may offer"
                    + " predefined options (short labels, at most five words each) and allow"
                    + " multiple selections; the user can always answer with free text. The"
                    + " recommended option is listed first and marked \"(Recommended)\" in its"
                    + " label. The turn pauses until the user answers.",
                AgentTool.schema("questions",
                    JsonSchema.builder().withType("array")
                            .withDescription("the questions to ask (usually exactly one)")
                            .withItems(questionSchema()).build()),
                args -> "[question is interactive and handled by the agent loop; it cannot be"
                    + " called directly]"),
            AgentTool.tool(KeYAgentTools.TOOL_SKILL, ToolCategory.INTERACTION,
                "Activates a user-defined skill by id. Skills add focused instructions to the"
                    + " system prompt of this and subsequent turns. Enabled only when the 'agent"
                    + " can use skills' setting is on.",
                AgentTool.schema("id",
                    JsonSchema.builder().withType("string")
                            .withDescription("the id of the skill to activate").build()),
                args -> "[skill is handled by the agent loop; it cannot be called directly]"));
    }

    /** The schema of one question object: {@code {question, header?, options?, multiple?}}. */
    private static JsonSchema questionSchema() {
        return JsonSchema.builder().withType("object")
                .addProperty("question",
                    JsonSchema.builder().withType("string")
                            .withDescription("the complete question text").build())
                .addProperty("header",
                    JsonSchema.builder().withType("string")
                            .withDescription("very short label of the question (at most 30"
                                + " characters)")
                            .build())
                .addProperty("options",
                    JsonSchema.builder().withType("array")
                            .withDescription("predefined answer options; the recommended one"
                                + " first, marked \"(Recommended)\"")
                            .withItems(JsonSchema.builder().withType("object")
                                    .addProperty("label",
                                        JsonSchema.builder().withType("string")
                                                .withDescription("concise display text (1-5"
                                                    + " words)")
                                                .build())
                                    .addProperty("description",
                                        JsonSchema.builder().withType("string")
                                                .withDescription("explanation of the option")
                                                .build())
                                    .build())
                            .build())
                .addProperty("multiple",
                    JsonSchema.builder().withType("boolean")
                            .withDescription("allow selecting several options (default false)")
                            .build())
                .build();
    }
}
