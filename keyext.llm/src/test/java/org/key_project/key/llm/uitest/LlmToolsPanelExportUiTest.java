/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.uitest;

import java.util.Comparator;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import javax.swing.JCheckBox;
import javax.swing.JRadioButton;

import org.key_project.key.llm.LlmSettings;
import org.key_project.key.llm.LlmToolsPanel;
import org.key_project.key.llm.mcp.Tool;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * UI test of the per-tool "export to MCP" checkboxes with an injected mock tool set: the initial
 * state follows the effective export rule and toggling writes the explicit override sets of the
 * settings working copy.
 */
class LlmToolsPanelExportUiTest {

    private final LlmSettings model = new LlmSettings(LlmSettings.INSTANCE);

    /** The mock tools in the same order the panel sorts them (category, then name). */
    private final List<Tool> tools = McpUiTestHarness.mockTools().stream()
            .sorted(Comparator.comparing((Tool t) -> t.category().ordinal())
                    .thenComparing(t -> t.function().name()))
            .toList();

    @BeforeEach
    void resetModel() {
        var s = LlmSettings.INSTANCE;
        model.setToolsDisabled(new TreeSet<>(s.getToolsDisabled()));
        model.setAllowedToolsWithApproval(new TreeSet<>(s.getAllowedToolsWithApproval()));
        model.setAllowedToolsWithoutApproval(new TreeSet<>(s.getAllowedToolsWithoutApproval()));
        model.setMcpExportedTools(new TreeSet<>(s.getMcpExportedTools()));
        model.setMcpNotExportedTools(new TreeSet<>(s.getMcpNotExportedTools()));
        McpUiTestHarness.resetSettings();
    }

    @Test
    void checkboxesReflectTheEffectiveExportRule() {
        var box = panelWith(model).exportCheckboxes();
        // order: mock_auth (PROOF), mock_read (FILES), mock_run (SHELL)
        assertTrue(box.get(0).isSelected(), "auto-approved tools are exported by default");
        assertTrue(box.get(1).isSelected());
        assertFalse(box.get(2).isSelected(), "ask-approved tools stay hidden by default");
    }

    @Test
    void approvalOverridesRecomputeTheDefaultExport() {
        model.setAllowedToolsWithoutApproval(new TreeSet<>(Set.of(McpUiTestHarness.MOCK_RUN)));
        model.setAllowedToolsWithApproval(new TreeSet<>(Set.of(McpUiTestHarness.MOCK_READ)));
        model.setToolsDisabled(new TreeSet<>(Set.of(McpUiTestHarness.MOCK_AUTH)));

        var box = panelWith(model).exportCheckboxes();
        assertFalse(box.get(0).isSelected(), "disabled tools are never exported");
        assertFalse(box.get(1).isSelected(), "with-approval AUTO tools are not exported");
        assertTrue(box.get(2).isSelected(),
            "without-approval ASK tools are exported by default");
    }

    @Test
    void explicitChoicesBeatTheDefaultInBothDirections() {
        model.setMcpExportedTools(new TreeSet<>(Set.of(McpUiTestHarness.MOCK_RUN)));
        model.setMcpNotExportedTools(
            new TreeSet<>(Set.of(McpUiTestHarness.MOCK_AUTH, McpUiTestHarness.MOCK_READ)));

        var box = panelWith(model).exportCheckboxes();
        assertFalse(box.get(0).isSelected(), "explicit exclusion wins over AUTO");
        assertFalse(box.get(1).isSelected());
        assertTrue(box.get(2).isSelected(), "explicit inclusion wins over ASK");
    }

    @Test
    void togglingWritesTheOverrideSets() {
        var panel = panelWith(model);
        var box = panel.exportCheckboxes();
        // mock_read is exported by default; unchecking it must record an explicit exclusion
        McpUiTestHarness.onEdt(() -> box.get(1).doClick());
        assertTrue(model.getMcpNotExportedTools().contains(McpUiTestHarness.MOCK_READ));
        assertFalse(model.getMcpExportedTools().contains(McpUiTestHarness.MOCK_READ));

        // checking an ask tool records an explicit inclusion
        McpUiTestHarness.onEdt(() -> box.get(2).doClick());
        assertTrue(model.getMcpExportedTools().contains(McpUiTestHarness.MOCK_RUN));
        assertTrue(panel.exportCheckboxes().get(2).isSelected());
    }

    @Test
    void permissionRadiosStillWriteTheApprovalSets() {
        var panel = panelWith(model);
        var disabled = McpUiTestHarness.all(panel.panel(),
            JRadioButton.class).stream().filter(r -> "Disabled".equals(r.getText())).findFirst()
                .orElseThrow();
        McpUiTestHarness.onEdt(disabled::doClick);
        assertEquals(Set.of(McpUiTestHarness.MOCK_AUTH), model.getToolsDisabled());
    }

    private static PanelWithCheckboxes panelWith(LlmSettings model) {
        var panel = new LlmToolsPanel(model, McpUiTestHarness.mockTools());
        return new PanelWithCheckboxes(panel);
    }

    private static final class PanelWithCheckboxes {
        private final LlmToolsPanel panel;

        private PanelWithCheckboxes(LlmToolsPanel panel) {
            this.panel = panel;
        }

        /** The "export to MCP" checkboxes in tool-sorted order. */
        private List<JCheckBox> exportCheckboxes() {
            return McpUiTestHarness.all(panel(), JCheckBox.class).stream()
                    .filter(c -> "export to MCP".equals(c.getText())).toList();
        }

        private LlmToolsPanel panel() {
            return panel;
        }
    }
}
