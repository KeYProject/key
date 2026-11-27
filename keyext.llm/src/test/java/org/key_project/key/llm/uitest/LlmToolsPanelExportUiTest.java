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
 * UI test of the per-tool "export to MCP" checkboxes with an injected mock tool set: the
 * KeY-specific
 * tools (Proof/Taclets) follow the effective export rule and toggling writes the explicit override
 * sets of the settings working copy, while the standard tools are disabled because they are never
 * exposed over the MCP server.
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
        // order: mock_auth (PROOF), mock_read (FILES), mock_run (SHELL), mock_add_taclet (TACLETS)
        assertTrue(box.get(0).isSelected() && box.get(0).isEnabled(),
            "auto-approved KeY-specific tools are exported by default");
        assertTrue(!box.get(1).isEnabled() && !box.get(1).isSelected(),
            "standard tools must never be exported");
        assertTrue(!box.get(2).isEnabled() && !box.get(2).isSelected());
        assertTrue(!box.get(3).isSelected() && box.get(3).isEnabled(),
            "ask-approved KeY-specific tools stay hidden by default");
    }

    @Test
    void approvalOverridesRecomputeTheDefaultExport() {
        model.setAllowedToolsWithoutApproval(new TreeSet<>(Set.of(McpUiTestHarness.MOCK_MUTATE)));
        model.setAllowedToolsWithApproval(new TreeSet<>(Set.of(McpUiTestHarness.MOCK_AUTH)));
        model.setToolsDisabled(new TreeSet<>(Set.of(McpUiTestHarness.MOCK_READ)));

        var box = panelWith(model).exportCheckboxes();
        assertFalse(box.get(0).isSelected(), "with-approval AUTO tools are not exported");
        assertTrue(!box.get(1).isEnabled() && !box.get(1).isSelected(),
            "standard tools stay off the MCP server even when disabled");
        assertTrue(!box.get(2).isEnabled() && !box.get(2).isSelected(),
            "standard tools stay off the MCP server regardless of approval");
        assertTrue(box.get(3).isSelected(),
            "without-approval ASK tools are exported by default");
    }

    @Test
    void explicitChoicesBeatTheDefaultInBothDirections() {
        model.setMcpExportedTools(new TreeSet<>(Set.of(McpUiTestHarness.MOCK_MUTATE)));
        model.setMcpNotExportedTools(
            new TreeSet<>(Set.of(McpUiTestHarness.MOCK_AUTH, McpUiTestHarness.MOCK_READ)));

        var box = panelWith(model).exportCheckboxes();
        assertFalse(box.get(0).isSelected(), "explicit exclusion wins over AUTO");
        assertTrue(!box.get(1).isEnabled() && !box.get(1).isSelected(),
            "an explicit export choice cannot enable a standard tool");
        assertTrue(box.get(3).isSelected(), "explicit inclusion wins over ASK");
    }

    @Test
    void togglingWritesTheOverrideSets() {
        var panel = panelWith(model);
        var box = panel.exportCheckboxes();
        // mock_auth is exported by default; unchecking it must record an explicit exclusion
        McpUiTestHarness.onEdt(() -> box.get(0).doClick());
        assertTrue(model.getMcpNotExportedTools().contains(McpUiTestHarness.MOCK_AUTH));
        assertFalse(model.getMcpExportedTools().contains(McpUiTestHarness.MOCK_AUTH));

        // checking an ask tool records an explicit inclusion
        McpUiTestHarness.onEdt(() -> box.get(3).doClick());
        assertTrue(model.getMcpExportedTools().contains(McpUiTestHarness.MOCK_MUTATE));
        assertTrue(panel.exportCheckboxes().get(3).isSelected());

        // a disabled standard checkbox is inert: clicking it writes no override
        McpUiTestHarness.onEdt(() -> box.get(1).doClick());
        McpUiTestHarness.onEdt(() -> box.get(2).doClick());
        assertFalse(model.getMcpExportedTools().contains(McpUiTestHarness.MOCK_READ));
        assertFalse(model.getMcpNotExportedTools().contains(McpUiTestHarness.MOCK_READ));
        assertFalse(model.getMcpExportedTools().contains(McpUiTestHarness.MOCK_RUN));
        assertFalse(model.getMcpNotExportedTools().contains(McpUiTestHarness.MOCK_RUN));
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
