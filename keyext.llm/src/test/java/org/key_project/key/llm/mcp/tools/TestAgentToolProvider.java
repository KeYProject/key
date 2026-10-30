/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.util.List;

import org.key_project.key.llm.mcp.AgentTool;
import org.key_project.key.llm.mcp.AgentToolProvider;

/**
 * Test-only tool set contributed through the {@link AgentToolProvider} service loader, to verify
 * that {@code KeYAgentTools} discovers tools from external providers (the test equivalent of a
 * plugin adding a tool).
 */
public class TestAgentToolProvider implements AgentToolProvider {
    public static final String EXTRA_TOOL = "echo_agent_test";
    public static final String EXTRA_DESC = "a test tool contributed via the AgentToolProvider"
        + " service loader that echoes its x argument";

    @Override
    public List<AgentTool> get() {
        return List.of(AgentTool.tool(EXTRA_TOOL, EXTRA_DESC,
            AgentTool.schema("x", org.key_project.key.llm.mcp.JsonSchema.builder()
                    .withType("string").build()),
            args -> "echo-agent:" + AgentTool.stringArg(args, "x")));
    }
}
