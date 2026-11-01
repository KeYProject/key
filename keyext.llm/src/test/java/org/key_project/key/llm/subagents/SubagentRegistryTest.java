/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.subagents;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests the sub-agent role registry: built-in roles are present, lookups and names work, and
 * every whitelist entry of every registered role refers to a tool that actually exists in the
 * tool registry (guards against typos in the role configurations).
 */
class SubagentRegistryTest {

    @Test
    void builtInRolesAreRegistered() {
        var roleNames = SubagentRegistry.INSTANCE.roleNames();
        assertTrue(roleNames.contains("goal-solver"), "missing goal-solver: " + roleNames);
        assertTrue(roleNames.contains("file-explorer"), "missing file-explorer: " + roleNames);
        assertTrue(roleNames.contains("rule-designer"), "missing rule-designer: " + roleNames);
        assertEquals(roleNames, roleNames.stream().sorted().toList(),
            "role names must be sorted");
    }

    @Test
    void getResolvesRoles() {
        var goalSolver = SubagentRegistry.INSTANCE.get("goal-solver");
        assertNotNull(goalSolver);
        assertNotNull(goalSolver.systemPrompt());
        assertTrue(goalSolver.parallelAllowed(), "goal-solver should allow parallel work");
        assertNull(SubagentRegistry.INSTANCE.get("no-such-role"));
        assertNull(SubagentRegistry.INSTANCE.get(null));
    }

    @Test
    void whitelistsReferToExistingTools() {
        // the full tool registry covers AgentTool-based tools and other MCP clients
        var toolNames = new org.key_project.key.llm.mcp.BuiltInMCPClient().getAllToolNames();
        for (var role : SubagentRegistry.INSTANCE.all()) {
            for (String tool : role.allowedTools()) {
                assertTrue(toolNames.contains(tool),
                    "role '" + role.name() + "' whitelists unknown tool '" + tool
                        + "' (available: " + toolNames + ")");
            }
        }
    }
}
