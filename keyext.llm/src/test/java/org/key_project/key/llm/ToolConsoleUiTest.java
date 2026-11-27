/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.function.BooleanSupplier;
import javax.swing.JTextField;
import javax.swing.tree.DefaultMutableTreeNode;

import org.key_project.key.llm.mcp.BuiltInMCPClient;
import org.key_project.key.llm.mcp.KeYAgentTools;
import org.key_project.key.llm.mcp.Tool;
import org.key_project.key.llm.mcp.tools.TestAgentToolProvider;
import org.key_project.key.llm.uitest.McpUiTestHarness;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * UI test of the tool console dialog with the real registry (which includes the test-only tools
 * of {@link TestMcpToolProvider} and the {@code TestAgentToolProvider}). The approval prompt is
 * a recording stub; decisions are queued per call. This test lives in package
 * {@code org.key_project.key.llm} because it drives the dialog's package-private test accessors.
 */
class ToolConsoleUiTest {

    private final Path outDir = Path.of("build", "ui-guide");

    /** Decisions served by the recording prompt; an empty queue denies. */
    private final Deque<ToolApprovalPrompt.Decision> decisions = new ArrayDeque<>();

    /** Tool calls the recording prompt has seen: {@code name|arguments}. */
    private final List<String> asked = new ArrayList<>();

    private ToolConsoleDialog dialog;

    @BeforeEach
    void setUp() {
        McpUiTestHarness.resetSettings();
        TestMcpToolProvider.reset();
        McpUiTestHarness.onEdt(() -> {
            dialog = new ToolConsoleDialog(null, new BuiltInMCPClient(), (tool, args) -> {
                asked.add(tool + "|" + args);
                return decisions.isEmpty() ? ToolApprovalPrompt.Decision.DENY : decisions.pop();
            });
        });
    }

    @AfterEach
    void tearDown() {
        McpUiTestHarness.resetSettings();
    }

    /** All tools currently shown as leaves of the dialog's tool tree. */
    private List<Tool> treeTools() {
        var model = (DefaultMutableTreeNode) dialog.toolTree().getModel().getRoot();
        var found = new ArrayList<Tool>();
        for (var category : java.util.Collections.list(model.children())) {
            for (var leaf : java.util.Collections.list(
                ((DefaultMutableTreeNode) category).children())) {
                if (leaf instanceof DefaultMutableTreeNode node
                        && node.getUserObject() instanceof Tool tool) {
                    found.add(tool);
                }
            }
        }
        return found;
    }

    /** Switches to the raw-JSON mode of the dialog. */
    private void enterJsonMode() {
        McpUiTestHarness.onEdt(() -> dialog.jsonToggle().doClick());
    }

    /** Waits until the condition holds (calls complete asynchronously on a worker thread). */
    private static void await(BooleanSupplier condition) throws InterruptedException {
        long deadline = System.currentTimeMillis() + 5000;
        while (!condition.getAsBoolean() && System.currentTimeMillis() < deadline) {
            Thread.sleep(20);
        }
        assertTrue(condition.getAsBoolean(), "condition not reached within the timeout");
    }

    @Test
    void treeShowsAllRegisteredToolsGroupedAndBadged() {
        var tools = treeTools();
        var names = tools.stream().map(t -> t.function().name()).toList();
        assertTrue(names.contains(TestMcpToolProvider.ECHO), names::toString);
        assertTrue(names.contains(TestMcpToolProvider.NEEDS_APPROVAL), names::toString);
        assertTrue(names.contains(TestAgentToolProvider.EXTRA_TOOL), names::toString);
        assertTrue(names.contains(KeYAgentTools.TOOL_READ), names::toString);
        // the badges reflect the effective approval policy
        var ask = tools.stream().filter(t -> t.function().name()
                .equals(TestMcpToolProvider.NEEDS_APPROVAL)).findFirst().orElseThrow();
        assertTrue(dialog.leafLabel(ask).endsWith("[ask]"), dialog.leafLabel(ask));
        var auto = tools.stream().filter(t -> t.function().name()
                .equals(TestMcpToolProvider.ECHO)).findFirst().orElseThrow();
        assertTrue(dialog.leafLabel(auto).endsWith("[auto]"), dialog.leafLabel(auto));
    }

    @Test
    void autoToolCallsWithoutPrompt() throws InterruptedException {
        assertTrue(dialog.selectToolByName(TestMcpToolProvider.ECHO));
        enterJsonMode();
        McpUiTestHarness.onEdt(() -> {
            dialog.jsonArea().setText("{\"x\":\"hi\"}");
            dialog.callButton().doClick();
        });
        await(() -> dialog.history().size() == 1);
        assertTrue(dialog.resultArea().getText().contains("echo:"),
            dialog.resultArea().getText());
        assertTrue(TestMcpToolProvider.EXECUTED.contains(TestMcpToolProvider.ECHO
            + "|{\"x\":\"hi\"}"), TestMcpToolProvider.EXECUTED::toString);
        assertTrue(dialog.resultArea().getText().contains("✓"), dialog.resultArea().getText());
        assertTrue(asked.isEmpty(), "auto tools never prompt: " + asked);
        assertEquals(1, dialog.history().size());
        assertEquals(TestMcpToolProvider.ECHO, dialog.history().get(0).tool());
    }

    @Test
    void askToolHonorsAllowOnce() throws InterruptedException {
        decisions.push(ToolApprovalPrompt.Decision.ALLOW_ONCE);
        assertTrue(dialog.selectToolByName(TestMcpToolProvider.NEEDS_APPROVAL));
        enterJsonMode();
        McpUiTestHarness.onEdt(() -> {
            dialog.jsonArea().setText("{\"n\":1}");
            dialog.callButton().doClick();
        });
        await(() -> dialog.resultArea().getText().contains("approved-tool-result"));
        assertEquals(List.of(TestMcpToolProvider.NEEDS_APPROVAL + "|{\"n\":1}"), asked);
        assertTrue(TestMcpToolProvider.EXECUTED.contains(TestMcpToolProvider.NEEDS_APPROVAL
            + "|{\"n\":1}"), TestMcpToolProvider.EXECUTED::toString);
    }

    @Test
    void denialPreventsTheCall() {
        assertTrue(dialog.selectToolByName(TestMcpToolProvider.NEEDS_APPROVAL));
        enterJsonMode();
        McpUiTestHarness.onEdt(() -> {
            dialog.jsonArea().setText("{}");
            dialog.callButton().doClick();
        });
        assertTrue(dialog.resultArea().getText().contains("denied"),
            dialog.resultArea().getText());
        assertTrue(TestMcpToolProvider.EXECUTED.isEmpty(), TestMcpToolProvider.EXECUTED::toString);
        assertTrue(asked.size() == 1, "the prompt was shown: " + asked);
        assertTrue(dialog.history().isEmpty(), "denials are not calls");
    }

    @Test
    void alwaysAllowPersistsAndRebadges() throws InterruptedException {
        decisions.push(ToolApprovalPrompt.Decision.ALWAYS);
        assertTrue(dialog.selectToolByName(TestMcpToolProvider.NEEDS_APPROVAL));
        enterJsonMode();
        McpUiTestHarness.onEdt(() -> {
            dialog.jsonArea().setText("{}");
            dialog.callButton().doClick();
        });
        await(() -> dialog.resultArea().getText().contains("approved-tool-result"));
        assertTrue(LlmSettings.INSTANCE.getAllowedToolsWithoutApproval()
                .contains(TestMcpToolProvider.NEEDS_APPROVAL));
        // the tree label follows the new policy without a restart
        var tool = treeTools().stream().filter(t -> t.function().name()
                .equals(TestMcpToolProvider.NEEDS_APPROVAL)).findFirst().orElseThrow();
        assertTrue(dialog.leafLabel(tool).endsWith("[auto]"), dialog.leafLabel(tool));
    }

    @Test
    void formsAndJsonModesStayInSync() {
        assertTrue(dialog.selectToolByName(TestAgentToolProvider.EXTRA_TOOL));
        var form = dialog.currentForm();
        assertNotNull(form);
        var field = assertInstanceOf(JTextField.class, form.editorOf("x"));
        // Forms → JSON
        McpUiTestHarness.onEdt(() -> {
            field.setText("hello");
            dialog.jsonToggle().doClick();
        });
        assertTrue(dialog.jsonArea().getText().contains("hello"),
            dialog.jsonArea().getText());
        assertTrue(dialog.jsonToggle().isSelected());
        // JSON → Forms
        McpUiTestHarness.onEdt(() -> {
            dialog.jsonArea().setText("{\"x\":\"world\"}");
            dialog.formsToggle().doClick();
        });
        assertEquals("world", field.getText());
        assertTrue(dialog.formsToggle().isSelected());
        // invalid JSON is reported inline and keeps the JSON mode
        McpUiTestHarness.onEdt(() -> dialog.jsonToggle().doClick());
        assertTrue(dialog.jsonToggle().isSelected());
        McpUiTestHarness.onEdt(() -> {
            dialog.jsonArea().setText("{not json");
            dialog.formsToggle().doClick();
        });
        assertTrue(dialog.jsonToggle().isSelected(), "the failed switch keeps the JSON mode");
        assertFalse(dialog.statusLabel().getText().isBlank(), "the error is reported inline");
    }

    @Test
    void searchFiltersTheToolTree() {
        McpUiTestHarness.onEdt(() -> dialog.searchField().setText("echo_"));
        assertEquals(2, treeTools().size(), treeTools().toString());
        McpUiTestHarness.onEdt(() -> dialog.searchField().setText(""));
        assertTrue(treeTools().size() > 2, "clearing the search restores all tools");
    }

    @Test
    void historyReloadsToolAndArguments() throws InterruptedException {
        assertTrue(dialog.selectToolByName(TestMcpToolProvider.ECHO));
        enterJsonMode();
        McpUiTestHarness.onEdt(() -> {
            dialog.jsonArea().setText("{\"x\":\"one\"}");
            dialog.callButton().doClick();
        });
        await(() -> dialog.history().size() == 1);
        // leave the tool via the search box, then reload the entry
        McpUiTestHarness.onEdt(() -> {
            dialog.searchField().setText("zzz-no-match");
            dialog.historyList().setSelectedIndex(0);
        });
        assertEquals(TestMcpToolProvider.ECHO, dialog.selectedTool().function().name());
        assertEquals("{\"x\":\"one\"}", dialog.currentForm().jsonEditor().getText());
    }

    @Test
    void renderConsolePng() throws Exception {
        assertTrue(dialog.selectToolByName(TestAgentToolProvider.EXTRA_TOOL));
        McpUiTestHarness.onEdt(() -> {
            try {
                // top-level windows do not paint headless; render the content pane instead
                McpUiTestHarness.render(dialog.getContentPane(),
                    outDir.resolve("tool-console.png"));
            } catch (java.io.IOException e) {
                throw new RuntimeException(e);
            }
        });
        assertTrue(java.nio.file.Files.exists(outDir.resolve("tool-console.png")));
    }
}
