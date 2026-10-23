/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.List;

import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.subagents.SubagentRole;
import org.key_project.key.llm.subagents.SubagentRoleProvider;

/**
 * Test-only sub-agent roles registered via a test {@code META-INF/services} entry. {@code
 * echo-role} only whitelists the test echo tool; {@code spawner-role} additionally whitelists
 * {@code spawn_subagent} so the depth guard can be exercised.
 */
public class TestSubagentRoleProvider implements SubagentRoleProvider {
    public static final String ECHO_ROLE = "echo-role";
    public static final String SPAWNER_ROLE = "spawner-role";

    @Override
    public List<SubagentRole> get() {
        return List.of(
            new SubagentRole(ECHO_ROLE, "test role that echoes", "Echo what you are asked.",
                List.of(TestMcpToolProvider.ECHO), null, 4, true),
            new SubagentRole(SPAWNER_ROLE, "test role that may spawn sub-agents",
                "You may delegate work to sub-agents.",
                List.of(KeYAgentTools.TOOL_SPAWN_SUBAGENT, TestMcpToolProvider.ECHO), null, 4,
                false));
    }
}
