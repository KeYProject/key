/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.uitest;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Set;
import java.util.TreeSet;
import javax.swing.AbstractButton;

import org.key_project.key.llm.LlmSettings;
import org.key_project.key.llm.LlmSettingsUI;
import org.key_project.key.llm.LlmStatusBar;
import org.key_project.key.llm.LlmToolsPanel;
import org.key_project.key.llm.mcp.KeYAgentTools;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Renders the screenshots used by the documentation ({@code docs/mcp-server.md} and the UI-test
 * protocol) into {@code keyext.llm/build/ui-guide/}. It is the automated part of the test protocol:
 * run it to regenerate the images, then copy the wanted ones into {@code docs/images/mcp/}.
 * Rendering happens headless through {@code JComponent.print} into a {@code BufferedImage}.
 */
class McpUiGuideTest {

    private final Path outDir = Path.of("build", "ui-guide");

    @Test
    void renderStatusBarOffState() throws Exception {
        render("mcp-statusbar-off.png", () -> {
            McpUiTestHarness.resetSettings();
            McpUiTestHarness.render(new LlmStatusBar(), outDir.resolve("mcp-statusbar-off.png"));
        });
    }

    @Test
    void renderStatusBarOnState() throws Exception {
        render("mcp-statusbar-on.png", () -> {
            McpUiTestHarness.resetSettings();
            LlmSettings.INSTANCE.setMcpServerHost("127.0.0.1");
            LlmSettings.INSTANCE.setMcpServerPort(0);
            var bar = new LlmStatusBar();
            var toggle = McpUiTestHarness.all(bar, AbstractButton.class).stream()
                    .filter(b -> "MCP".equals(b.getText())).findFirst().orElseThrow();
            toggle.doClick();
            // hovering shows the endpoint URL; keep it visible for the screenshot
            McpUiTestHarness.hover(toggle, true);
            McpUiTestHarness.render(bar, outDir.resolve("mcp-statusbar-on.png"));
            McpUiTestHarness.hover(toggle, false);
            toggle.doClick();
        });
    }

    @Test
    void renderToolsExportPanel() throws Exception {
        render("mcp-tools-export.png", () -> {
            McpUiTestHarness.resetSettings();
            var model = new LlmSettings(LlmSettings.INSTANCE);
            // show both directions of the override feature in the picture
            model.setMcpExportedTools(new TreeSet<>(Set.of(KeYAgentTools.TOOL_RUN_COMMAND)));
            model.setMcpNotExportedTools(new TreeSet<>(Set.of(KeYAgentTools.TOOL_READ_FILE)));
            McpUiTestHarness.render(new LlmToolsPanel(model),
                outDir.resolve("mcp-tools-export.png"));
        });
    }

    @Test
    void renderSettingsMcpServerSection() throws Exception {
        render("mcp-server-settings.png", () -> {
            McpUiTestHarness.resetSettings();
            var model = new LlmSettings(LlmSettings.INSTANCE);
            model.setMcpServerEnabled(true);
            model.setMcpServerHost("127.0.0.1");
            model.setMcpServerPort(44884);
            model.setMcpServerToken("");
            McpUiTestHarness.render(new LlmSettingsUI(model),
                outDir.resolve("mcp-server-settings.png"));
        });
    }

    @Test
    void endpointLabelShowsOnHoverAndHidesOnLeave() throws Exception {
        // guards the on-state screenshot: the endpoint label must actually be visible
        renderOnEdt(() -> {
            McpUiTestHarness.resetSettings();
            LlmSettings.INSTANCE.setMcpServerHost("127.0.0.1");
            LlmSettings.INSTANCE.setMcpServerPort(0);
            var bar = new LlmStatusBar();
            var toggle = McpUiTestHarness.all(bar, AbstractButton.class).stream()
                    .filter(b -> "MCP".equals(b.getText())).findFirst().orElseThrow();
            toggle.doClick();
            try {
                // the endpoint URL is hover-only: hovering must reveal it
                McpUiTestHarness.hover(toggle, true);
                var label = McpUiTestHarness.all(bar, javax.swing.text.JTextComponent.class)
                        .stream().filter(l -> l.isVisible() && l.getText() != null
                                && l.getText().startsWith("http://"))
                        .findFirst().orElse(null);
                assertTrue(label != null, "endpoint label must be visible while hovering");
                McpUiTestHarness.hover(toggle, false);
                var labelAfter = McpUiTestHarness.all(bar,
                    javax.swing.text.JTextComponent.class).stream().filter(l -> l.isVisible())
                        .filter(l -> l.getText() != null && l.getText().startsWith("http://"))
                        .findFirst().orElse(null);
                assertTrue(labelAfter == null, "endpoint label must hide when the pointer leaves");
            } finally {
                toggle.doClick();
            }
        });
    }

    /** Renders the task on the EDT and asserts the produced PNG is non-trivial. */
    private void render(String file, ThrowingRunnable task) throws Exception {
        renderOnEdt(task);
        Path png = outDir.resolve(file);
        assertTrue(Files.size(png) > 1_000, png + " must be a non-empty PNG");
    }

    private void renderOnEdt(ThrowingRunnable task) {
        McpUiTestHarness.onEdt(() -> {
            try {
                task.run();
            } catch (Exception e) {
                throw new RuntimeException(e);
            }
        });
    }

    private interface ThrowingRunnable {
        void run() throws Exception;
    }
}
