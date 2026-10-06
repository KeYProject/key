/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import javax.swing.*;

import de.uka.ilkd.key.gui.settings.SettingsPanel;

import org.key_project.key.llm.mcp.BuiltInMCPClient;

/**
 * Settings panel for the KeY-Agent tool approval/disablement table. It is shown as its own node
 * ("Tools") under "LLM Settings" in the settings dialog and edits a working copy of
 * {@link LlmSettings}; {@link #getModel()} hands that copy to the settings provider for applying.
 *
 * @author Alexander Weigl
 */
public class LlmToolsPanel extends SettingsPanel {
    private final LlmSettings model;
    private final JTable table;

    public LlmToolsPanel(LlmSettings model) {
        this.model = model;

        addSeparator("Tools");
        var mcpClient = new BuiltInMCPClient().getAllToolNames().stream().toList();
        var name = new Column<String, String>("Name", String.class, s -> s);
        var disabled = new Column<String, Boolean>("Disabled", Boolean.class,
            model.getToolsDisabled()::contains,
            (s, value) -> {
                if (value == Boolean.TRUE) {
                    model.getToolsDisabled().add(s);
                } else {
                    model.getToolsDisabled().remove(s);
                }
            });
        var withApproval = new Column<String, Boolean>("With approval", Boolean.class,
            model.getAllowedToolsWithApproval()::contains,
            (s, value) -> {
                if (value == Boolean.TRUE) {
                    model.getAllowedToolsWithApproval().add(s);
                } else {
                    model.getAllowedToolsWithApproval().remove(s);
                }
            });
        var withoutApproval =
            new Column<String, Boolean>("Without approval (always)", Boolean.class,
                model.getAllowedToolsWithoutApproval()::contains,
                (s, value) -> {
                    if (value == Boolean.TRUE) {
                        model.getAllowedToolsWithoutApproval().add(s);
                    } else {
                        model.getAllowedToolsWithoutApproval().remove(s);
                    }
                });
        table = addTableBox("Tools", "Disable tools, or change their approval"
            + " behavior. Disabled tools are not sent to the model at all.", mcpClient, name,
            disabled, withApproval, withoutApproval);

        // Set checkbox editor and renderer for boolean columns
        table.setDefaultEditor(Boolean.class, new DefaultCellEditor(new JCheckBox()));
        table.setDefaultRenderer(Boolean.class,
            new javax.swing.table.DefaultTableCellRenderer() {
                @Override
                public java.awt.Component getTableCellRendererComponent(JTable table, Object value,
                        boolean isSelected, boolean hasFocus, int row, int column) {
                    JCheckBox checkBox = new JCheckBox();
                    if (value instanceof Boolean bool) {
                        checkBox.setSelected(bool);
                    }
                    checkBox.setHorizontalAlignment(JLabel.CENTER);
                    if (isSelected) {
                        checkBox.setBackground(table.getSelectionBackground());
                        checkBox.setForeground(table.getSelectionForeground());
                    } else {
                        checkBox.setBackground(table.getBackground());
                        checkBox.setForeground(table.getForeground());
                    }
                    return checkBox;
                }
            });
    }

    /** The working copy of the settings edited by this panel. */
    public LlmSettings getModel() {
        return model;
    }
}
