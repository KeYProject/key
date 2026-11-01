/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.Set;
import java.util.TreeSet;

import org.key_project.key.llm.mcp.KeYAgentTools;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests the MCP-server related settings: the default export rule, the explicit per-tool export
 * overrides, the copy constructor carrying the new fields, and headless construction of the UI
 * panels that edit them.
 */
class LlmMcpSettingsTest {

    private final LlmSettings settings = LlmSettings.INSTANCE;

    @BeforeEach
    void reset() {
        settings.setToolsDisabled(new TreeSet<>());
        settings.setAllowedToolsWithApproval(new TreeSet<>());
        settings.setAllowedToolsWithoutApproval(new TreeSet<>());
        settings.setMcpExportedTools(new TreeSet<>());
        settings.setMcpNotExportedTools(new TreeSet<>());
    }

    @Test
    void metadataApprovalGovernsTheDefaultExport() {
        // read_file is AUTO by metadata -> exported by default; run_command is ASK -> not
        assertTrue(settings.isExportedToMCPByDefault(KeYAgentTools.TOOL_READ_FILE, true));
        assertFalse(settings.isExportedToMCPByDefault(KeYAgentTools.TOOL_RUN_COMMAND, false));
    }

    @Test
    void approvalSettingsAdjustTheDefaultExport() {
        // an ASK tool the user approves without asking becomes exported by default
        settings.setAllowedToolsWithoutApproval(
            new TreeSet<>(Set.of(KeYAgentTools.TOOL_RUN_COMMAND)));
        assertTrue(settings.isExportedToMCPByDefault(KeYAgentTools.TOOL_RUN_COMMAND, false));

        // an AUTO tool the user wants confirmed is no longer exported by default
        settings.setAllowedToolsWithApproval(new TreeSet<>(Set.of(KeYAgentTools.TOOL_READ_FILE)));
        assertFalse(settings.isExportedToMCPByDefault(KeYAgentTools.TOOL_READ_FILE, true));

        // a disabled tool is never exported by default
        settings.setToolsDisabled(new TreeSet<>(Set.of(KeYAgentTools.TOOL_READ_FILE)));
        assertFalse(settings.isExportedToMCPByDefault(KeYAgentTools.TOOL_READ_FILE, true));
    }

    @Test
    void explicitExportChoicesBeatTheDefault() {
        assertTrue(settings.isExportedToMCP(KeYAgentTools.TOOL_READ_FILE, true));
        assertFalse(settings.isExportedToMCP(KeYAgentTools.TOOL_RUN_COMMAND, false));

        settings.setMcpNotExportedTools(new TreeSet<>(Set.of(KeYAgentTools.TOOL_READ_FILE)));
        settings.setMcpExportedTools(new TreeSet<>(Set.of(KeYAgentTools.TOOL_RUN_COMMAND)));
        assertFalse(settings.isExportedToMCP(KeYAgentTools.TOOL_READ_FILE, true));
        assertTrue(settings.isExportedToMCP(KeYAgentTools.TOOL_RUN_COMMAND, false));
    }

    @Test
    void copyConstructorCarriesTheMcpServerFields() {
        settings.setMcpServerEnabled(true);
        settings.setMcpServerHost("0.0.0.0");
        settings.setMcpServerPort(4242);
        settings.setMcpServerToken("tok");
        settings.setMcpExportedTools(new TreeSet<>(Set.of("a")));
        settings.setMcpNotExportedTools(new TreeSet<>(Set.of("b")));

        var copy = new LlmSettings(settings);
        assertTrue(copy.getMcpServerEnabled());
        assertEquals("0.0.0.0", copy.getMcpServerHost());
        assertEquals(4242, copy.getMcpServerPort());
        assertEquals("tok", copy.getMcpServerToken());
        assertEquals(Set.of("a"), copy.getMcpExportedTools());
        assertEquals(Set.of("b"), copy.getMcpNotExportedTools());
    }

    @Test
    void uiPanelsConstructHeadless() {
        assertDoesNotThrow(() -> {
            assertNotNull(new LlmToolsPanel(new LlmSettings(LlmSettings.INSTANCE)));
            assertNotNull(new LlmSettingsUI(new LlmSettings(LlmSettings.INSTANCE)));
            assertNotNull(new LlmStatusBar());
        });
    }
}
