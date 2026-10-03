/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.List;
import java.util.concurrent.CopyOnWriteArrayList;

import org.key_project.key.llm.mcp.FunctionDefinition;
import org.key_project.key.llm.mcp.JsonSchema;
import org.key_project.key.llm.mcp.McpClient;
import org.key_project.key.llm.mcp.McpToolProvider;
import org.key_project.key.llm.mcp.Tool;

/**
 * Test-only tool set registered via a test {@code META-INF/services} entry. Provides two tools:
 * an auto-approved echo and a tool that requires approval by default.
 */
public class TestMcpToolProvider implements McpToolProvider {
    public static final String ECHO = "echo_test";
    public static final String NEEDS_APPROVAL = "needs_approval_test";

    /** Records every executed call as {@code name|arguments}. */
    public static final List<String> EXECUTED = new CopyOnWriteArrayList<>();

    public static void reset() {
        EXECUTED.clear();
    }

    private final McpClient client = new McpClient() {
        @Override
        public List<Tool> getTools() {
            return List.of(
                new Tool(new FunctionDefinition(ECHO, "echoes the x argument",
                    new JsonSchema("object"))),
                new Tool(new FunctionDefinition(NEEDS_APPROVAL, "a tool that needs approval",
                    new JsonSchema("object")), Tool.ApprovalRequirement.ASK));
        }

        @Override
        public Object callTool(String toolName, String arguments) {
            EXECUTED.add(toolName + "|" + arguments);
            return switch (toolName) {
                case ECHO -> "echo:" + arguments;
                case NEEDS_APPROVAL -> "approved-tool-result";
                default -> "unknown";
            };
        }

        @Override
        public boolean isClosed() {
            return false;
        }

        @Override
        public void close() {
        }
    };

    @Override
    public List<McpClient> get() {
        return List.of(client);
    }
}
