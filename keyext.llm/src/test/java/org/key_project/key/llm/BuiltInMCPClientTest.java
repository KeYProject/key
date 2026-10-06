/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.Set;
import java.util.TreeSet;

import org.key_project.key.llm.mcp.BuiltInMCPClient;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.McpToolNowAllowedException;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests the built-in tool registry: disabled filtering and the live approval decisions, including
 * the regression that {@code getTools()} must never mutate the approval settings.
 */
class BuiltInMCPClientTest {

    private BuiltInMCPClient client;

    @BeforeEach
    void setUp() {
        LlmSettings.INSTANCE.setToolsDisabled(new TreeSet<>());
        LlmSettings.INSTANCE.setAllowedToolsWithApproval(new TreeSet<>());
        LlmSettings.INSTANCE.setAllowedToolsWithoutApproval(new TreeSet<>());
        client = new BuiltInMCPClient();
    }

    private static Set<String> toolNames(BuiltInMCPClient c) {
        var names = new TreeSet<String>();
        c.getTools().forEach(t -> names.add(t.function().name()));
        return names;
    }

    @Test
    void advertisesBuiltInAndTestTools() {
        var names = toolNames(client);
        assertTrue(names.contains(KeYAgentTools.TOOL_READ_FILE));
        assertTrue(names.contains(KeYAgentTools.TOOL_RUN_COMMAND));
        assertTrue(names.contains(KeYAgentTools.TOOL_ASK_USER));
        assertTrue(names.contains(KeYAgentTools.TOOL_GET_PROOF_CONTEXT));
        assertTrue(names.contains(KeYAgentTools.TOOL_TRYCLOSE));
        assertTrue(names.contains(KeYAgentTools.TOOL_AUTO));
        assertTrue(names.contains(TestMcpToolProvider.ECHO));
        assertTrue(names.contains(TestMcpToolProvider.NEEDS_APPROVAL));
    }

    @Test
    void getToolsDoesNotMutateApprovalSets() {
        LlmSettings.INSTANCE.setAllowedToolsWithApproval(new TreeSet<>(Set.of("x")));
        LlmSettings.INSTANCE.setAllowedToolsWithoutApproval(new TreeSet<>(Set.of("y")));
        var before = client.getAllToolNames();
        var first = toolNames(client);
        var second = toolNames(client);
        // getTools() must be side-effect free
        assertTrue(first.equals(second), "getTools() produced different results on repeat calls");
        assertTrue(client.getAllToolNames().equals(before));
        assertTrue(LlmSettings.INSTANCE.getAllowedToolsWithApproval().equals(Set.of("x")));
        assertTrue(LlmSettings.INSTANCE.getAllowedToolsWithoutApproval().equals(Set.of("y")));
    }

    @Test
    void disabledToolsAreFilteredOut() {
        LlmSettings.INSTANCE.setToolsDisabled(new TreeSet<>(Set.of(TestMcpToolProvider.ECHO)));
        var names = toolNames(client);
        assertFalse(names.contains(TestMcpToolProvider.ECHO));
        assertTrue(names.contains(KeYAgentTools.TOOL_READ_FILE));
        assertTrue(client.isDisabled(TestMcpToolProvider.ECHO));
    }

    @Test
    void disabledToolCannotBeInvoked() {
        LlmSettings.INSTANCE.setToolsDisabled(new TreeSet<>(Set.of(TestMcpToolProvider.ECHO)));
        assertThrows(McpToolNowAllowedException.class,
            () -> client.callTool(TestMcpToolProvider.ECHO, "{}"));
    }

    @Test
    void defaultApprovalRequirements() {
        // read-only built-ins are AUTO
        assertFalse(client.requiresApproval(KeYAgentTools.TOOL_READ_FILE));
        assertFalse(client.requiresApproval(KeYAgentTools.TOOL_LIST_FILES));
        assertFalse(client.requiresApproval(KeYAgentTools.TOOL_GET_PROOF_CONTEXT));
        assertFalse(client.requiresApproval(KeYAgentTools.TOOL_ASK_USER));
        assertFalse(client.requiresApproval(KeYAgentTools.TOOL_TRYCLOSE));
        assertFalse(client.requiresApproval(KeYAgentTools.TOOL_AUTO));
        assertFalse(client.requiresApproval(TestMcpToolProvider.ECHO));
        // shell execution and aimless test tools are ASK by default
        assertTrue(client.requiresApproval(KeYAgentTools.TOOL_RUN_COMMAND));
        assertTrue(client.requiresApproval(TestMcpToolProvider.NEEDS_APPROVAL));
    }

    @Test
    void userConfiguredOverridesBeatDefaults() {
        // allowedToolsWithoutApproval overrides an ASK tool
        var without = new TreeSet<>(LlmSettings.INSTANCE.getAllowedToolsWithoutApproval());
        without.add(KeYAgentTools.TOOL_RUN_COMMAND);
        LlmSettings.INSTANCE.setAllowedToolsWithoutApproval(without);
        assertFalse(client.requiresApproval(KeYAgentTools.TOOL_RUN_COMMAND));

        // allowedToolsWithApproval overrides an AUTO tool
        var with = new TreeSet<>(LlmSettings.INSTANCE.getAllowedToolsWithApproval());
        with.add(KeYAgentTools.TOOL_READ_FILE);
        LlmSettings.INSTANCE.setAllowedToolsWithApproval(with);
        assertTrue(client.requiresApproval(KeYAgentTools.TOOL_READ_FILE));
    }

    @Test
    void unknownToolsRequireApproval() {
        // conservative default: refuse to run tools we do not even know
        assertTrue(client.requiresApproval("no_such_tool"));
    }
}
