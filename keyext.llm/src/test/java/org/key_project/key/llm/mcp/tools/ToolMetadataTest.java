/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.Tool;
import org.key_project.key.llm.mcp.ToolCategory;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests the category and background metadata of the tool set: defaults, explicit values, the
 * grouping/sorting of the Markdown documentation and the JSON CLI output that carries the
 * KeY-side metadata.
 */
class ToolMetadataTest {

    @Test
    void metadataDefaultsToGeneralAndSynchronous() {
        var tool = AgentTool.tool("plain", "a plain tool", args -> "ok");
        assertEquals(ToolCategory.GENERAL, tool.category());
        assertFalse(tool.backgroundable());
        // the Tool record (as seen by the settings UI) mirrors the metadata
        var asTool = tool.asTool();
        assertEquals(ToolCategory.GENERAL, asTool.category());
        assertFalse(asTool.backgroundable());
    }

    @Test
    void explicitCategoryAndBackgroundFlagAreCarried() {
        var tool = AgentTool.tool("auto", ToolCategory.PROOF, "runs the auto strategy",
            AgentTool.schema("steps", org.key_project.key.llm.mcp.JsonSchema.builder()
                    .withType("integer").build()),
            true,
            args -> "done");
        assertEquals(ToolCategory.PROOF, tool.category());
        assertTrue(tool.backgroundable());
        assertEquals(ToolCategory.PROOF, tool.asTool().category());
        assertTrue(tool.asTool().backgroundable());
    }

    @Test
    void wireFormatDoesNotLeakCategoryMetadata() {
        var tool = new Tool(new org.key_project.key.llm.mcp.FunctionDefinition("run_command",
            "runs a command",
            new org.key_project.key.llm.mcp.JsonSchema("object")),
            Tool.ApprovalRequirement.ASK, ToolCategory.SHELL, true);
        var map = tool.toMap();
        assertFalse(map.containsKey("category"), "category must not be sent to the model");
        assertFalse(map.containsKey("backgroundable"),
            "backgroundable must not be sent to the model");
    }

    @Test
    void everyBuiltInToolHasACategory() {
        var tools = new KeYAgentTools();
        for (var agent : tools.agents()) {
            assertEquals(agent.category(), agent.asTool().category(),
                "metadata must be consistent for " + agent.name());
        }
        // spot-check the assignments
        assertEquals(ToolCategory.PROOF, tools.agent(KeYAgentTools.TOOL_AUTO).category());
        assertEquals(ToolCategory.SHELL, tools.agent(KeYAgentTools.TOOL_RUN_COMMAND).category());
        assertEquals(ToolCategory.TACLETS, tools.agent(KeYAgentTools.TOOL_LIST_TACLETS).category());
        assertEquals(ToolCategory.INTERACTION, tools.agent(KeYAgentTools.TOOL_ASK_USER).category());
        assertEquals(ToolCategory.SUBAGENTS,
            tools.agent(KeYAgentTools.TOOL_SPAWN_SUBAGENT).category());
        assertEquals(ToolCategory.DOCUMENTATION,
            tools.agent(KeYAgentTools.TOOL_LIST_TOOLS).category());
        assertEquals(ToolCategory.FILES, tools.agent(KeYAgentTools.TOOL_LIST_FILES).category());
    }

    @Test
    void onlyLongRunningToolsAreBackgroundableByDefault() {
        var tools = new KeYAgentTools();
        for (var name : java.util.List.of(KeYAgentTools.TOOL_RUN_COMMAND, KeYAgentTools.TOOL_AUTO,
            KeYAgentTools.TOOL_TRYCLOSE, KeYAgentTools.TOOL_SPAWN_SUBAGENT)) {
            assertTrue(tools.agent(name).backgroundable(),
                "tool " + name + " must default to backgroundable");
        }
        for (var name : java.util.List.of(KeYAgentTools.TOOL_READ_FILE, KeYAgentTools.TOOL_ASK_USER,
            KeYAgentTools.TOOL_LIST_TOOLS, KeYAgentTools.TOOL_GET_SUBAGENT_LOGS)) {
            assertFalse(tools.agent(name).backgroundable(),
                "tool " + name + " must not default to backgroundable");
        }
    }

    @Test
    void markdownDocumentationIsGroupedByCategory() {
        var tools = new KeYAgentTools();
        var doc = tools.toolsMarkdown();
        // headers per category, in order
        assertTrue(doc.indexOf("## Proof") < doc.indexOf("## Files"), doc);
        assertTrue(doc.indexOf("## Files") < doc.indexOf("## Shell"), doc);
        assertTrue(doc.indexOf("## Shell") < doc.indexOf("## Taclets"), doc);
        assertTrue(doc.indexOf("## Taclets") < doc.indexOf("## Sub-agents"), doc);
        // each tool appears in its category section (marked with the category in the heading)
        assertTrue(doc.contains("`" + KeYAgentTools.TOOL_AUTO + "` (AUTO · Proof"),
            "auto must be documented under Proof:\n" + doc);
        assertTrue(doc.contains("`" + KeYAgentTools.TOOL_RUN_COMMAND + "` (ASK · Shell"),
            "run_command must be documented under Shell:\n" + doc);
        // background flag is rendered on the backgroundable tools themselves
        assertTrue(doc.contains("`" + KeYAgentTools.TOOL_RUN_COMMAND
            + "` (ASK · Shell) · can run in background"), doc);
    }
}
