/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.uitest;

import java.util.Map;
import java.util.stream.Collectors;

import org.key_project.key.llm.LlmSettings;
import org.key_project.key.llm.LlmStatusBar;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.tools.TestAgentToolProvider;

import io.modelcontextprotocol.client.transport.HttpClientSseClientTransport;
import io.modelcontextprotocol.spec.McpSchema;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * UI test of the {@link LlmStatusBar} status-line indicator: an actual MCP client interacts with
 * the server started through the toggle button while the endpoint label is on, and the toggle/flag
 * state is verified across the whole lifecycle including the persisted restart path.
 */
class LlmStatusBarUiTest {

    private LlmStatusBar bar;
    private javax.swing.JToggleButton toggle;

    @BeforeEach
    void setUp() {
        McpUiTestHarness.resetSettings();
        LlmSettings.INSTANCE.setMcpServerHost("127.0.0.1");
        LlmSettings.INSTANCE.setMcpServerPort(0);
        McpUiTestHarness.onEdt(() -> bar = new LlmStatusBar());
        toggle = McpUiTestHarness.all(bar, javax.swing.JToggleButton.class).stream()
                .filter(b -> "MCP".equals(b.getText())).findFirst().orElseThrow();
    }

    @AfterEach
    void tearDown() {
        if (bar != null) {
            McpUiTestHarness.onEdt(() -> {
                if (toggle.isSelected()) {
                    toggle.doClick();
                }
            });
        }
        McpUiTestHarness.resetSettings();
    }

    @Test
    void toggleStartsAndStopsTheServerAndSyncsTheSettingsFlag() {
        // initially off
        assertFalse(toggle.isSelected());
        assertFalse(serverRunning());

        McpUiTestHarness.onEdt(() -> toggle.doClick());

        // server running, endpoint label visible, persisted flag set
        assertTrue(toggle.isSelected());
        assertTrue(serverRunning());
        assertTrue(LlmSettings.INSTANCE.getMcpServerEnabled());
        String endpoint = endpointLabel();
        assertNotNull(endpoint);
        assertTrue(endpoint.matches("http://127\\.0\\.0\\.1:\\d+/sse"), "endpoint " + endpoint);

        McpUiTestHarness.onEdt(() -> toggle.doClick());

        // server stopped again
        assertFalse(toggle.isSelected());
        assertFalse(serverRunning());
        assertFalse(LlmSettings.INSTANCE.getMcpServerEnabled());
        assertFalse(endpointVisible());
    }

    @Test
    void serverAnswersAnMcpClientWhileTheStatusBarShowsTheEndpoint() throws Exception {
        McpUiTestHarness.onEdt(() -> toggle.doClick());
        String endpoint = endpointLabel();
        assertNotNull(endpoint);

        var transport = HttpClientSseClientTransport.builder(endpoint).build();
        var client = io.modelcontextprotocol.client.McpClient.sync(transport)
                .clientInfo(new McpSchema.Implementation("LlmStatusBarUiTest", "1.0"))
                .build();
        try {
            client.initialize();
            var names = client.listTools().tools().stream().map(McpSchema.Tool::name)
                    .collect(Collectors.toSet());
            assertTrue(names.contains(KeYAgentTools.TOOL_READ_FILE),
                "auto-approved tools must be served, got " + names);
            assertTrue(names.contains(TestAgentToolProvider.EXTRA_TOOL));
            assertFalse(names.contains(KeYAgentTools.TOOL_RUN_COMMAND),
                "ask-approved tools must stay hidden, got " + names);

            var result = client.callTool(McpSchema.CallToolRequest
                    .builder(TestAgentToolProvider.EXTRA_TOOL).arguments(Map.of("x", "ui"))
                    .build());
            assertTrue(result.content().get(0) instanceof McpSchema.TextContent);
            assertEquals("echo-agent:ui",
                ((McpSchema.TextContent) result.content().get(0)).text());

            // the client interaction must not have disturbed the status bar
            assertTrue(toggle.isSelected());
            assertTrue(endpointVisible());
        } finally {
            client.close();
        }
    }

    @Test
    void restoreReplaysAPreviouslyEnabledServer() {
        assertFalse(serverRunning());
        LlmSettings.INSTANCE.setMcpServerEnabled(true);

        McpUiTestHarness.onEdt(() -> bar.maybeRestore());
        McpUiTestHarness.onEdt(() -> {
            /* flush the restore's invokeLater */ });

        assertTrue(toggle.isSelected());
        assertTrue(serverRunning());
        assertNotNull(endpointLabel());
    }

    private boolean serverRunning() {
        String endpoint = endpointLabel();
        if (endpoint == null) {
            return false;
        }
        // independent of the settings flag: does something actually listen on the endpoint port?
        try (java.net.Socket s =
            new java.net.Socket("127.0.0.1", java.net.URI.create(endpoint).getPort())) {
            return true;
        } catch (java.io.IOException e) {
            return false;
        }
    }

    private boolean endpointVisible() {
        return McpUiTestHarness.all(bar, javax.swing.JLabel.class).stream()
                .anyMatch(
                    l -> l.isVisible() && l.getText() != null && l.getText().startsWith("http://"));
    }

    private String endpointLabel() {
        return McpUiTestHarness.all(bar, javax.swing.JLabel.class).stream()
                .map(javax.swing.JLabel::getText).filter(t -> t != null && t.startsWith("http://"))
                .findFirst().orElse(null);
    }
}
