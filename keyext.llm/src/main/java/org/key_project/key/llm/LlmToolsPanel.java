/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.awt.FlowLayout;
import java.util.EnumMap;
import javax.swing.*;

import de.uka.ilkd.key.gui.settings.SettingsPanel;

import org.key_project.key.llm.mcp.BuiltInMCPClient;
import org.key_project.key.llm.mcp.Tool;

import net.miginfocom.swing.MigLayout;

/**
 * Settings panel for the KeY-Agent tool permissions. It is shown as its own node ("Tools") under
 * "LLM Settings" in the settings dialog and edits a working copy of {@link LlmSettings}. Every tool
 * gets one row with a short explanation and a radio group selecting its permission (default, with
 * approval, without approval, disabled); {@link #getModel()} hands the copy to the settings
 * provider for applying.
 *
 * @author Alexander Weigl
 */
public class LlmToolsPanel extends SettingsPanel {
    /** The permission of a tool as configured in the settings. */
    private enum Permission {
        DEFAULT, WITH_APPROVAL, WITHOUT_APPROVAL, DISABLED
    }

    private final LlmSettings model;

    public LlmToolsPanel(LlmSettings model) {
        this.model = model;

        setHeaderText("Tools");
        setSubHeaderText("Control which tools the KeY-Agent may call and whether they require"
            + " approval. Disabled tools are not sent to the model at all.");

        var mcpClient = new BuiltInMCPClient();
        for (var tool : mcpClient.getAllTools()) {
            addTitledComponent(tool.function().name(), toolBlock(tool),
                tool.function().description());
        }
    }

    /** The row for one tool: its explanation plus the permission radio group. */
    private JComponent toolBlock(Tool tool) {
        var name = tool.function().name();

        var description = new JTextArea(tool.function().description());
        description.setEditable(false);
        description.setFocusable(false);
        description.setOpaque(false);
        description.setLineWrap(true);
        description.setWrapStyleWord(true);
        description.setBorder(BorderFactory.createEmptyBorder());
        description.setForeground(UIManager.getColor("Label.disabledForeground"));

        var defaultLabel = tool.defaultApproval() == Tool.ApprovalRequirement.ASK
                ? "Default (ask)"
                : "Default (auto)";
        var group = new ButtonGroup();
        var buttons = new EnumMap<Permission, JRadioButton>(Permission.class);
        buttons.put(Permission.DEFAULT, radio(group, defaultLabel));
        buttons.put(Permission.WITH_APPROVAL, radio(group, "With approval"));
        buttons.put(Permission.WITHOUT_APPROVAL, radio(group, "Without approval (always)"));
        buttons.put(Permission.DISABLED, radio(group, "Disabled"));

        var radios = new JPanel(new FlowLayout(FlowLayout.LEFT, 12, 0));
        for (var button : buttons.values()) {
            radios.add(button);
        }

        buttons.get(currentPermission(name)).setSelected(true);
        for (var entry : buttons.entrySet()) {
            var permission = entry.getKey();
            entry.getValue().addActionListener(e -> applyPermission(name, permission));
        }

        var block = new JPanel(new MigLayout("insets 0, gapy 2"));
        block.add(description, "span, growx, wrap");
        block.add(radios, "span, growx");
        return block;
    }

    private static JRadioButton radio(ButtonGroup group, String text) {
        var button = new JRadioButton(text);
        group.add(button);
        return button;
    }

    /** The permission that matches the current configuration of the working copy. */
    private Permission currentPermission(String toolName) {
        if (model.getToolsDisabled().contains(toolName)) {
            return Permission.DISABLED;
        }
        if (model.getAllowedToolsWithoutApproval().contains(toolName)) {
            return Permission.WITHOUT_APPROVAL;
        }
        if (model.getAllowedToolsWithApproval().contains(toolName)) {
            return Permission.WITH_APPROVAL;
        }
        return Permission.DEFAULT;
    }

    /** Writes the chosen permission into the (mutually exclusive) tool sets of the working copy. */
    private void applyPermission(String toolName, Permission permission) {
        var disabled = model.getToolsDisabled();
        var with = model.getAllowedToolsWithApproval();
        var without = model.getAllowedToolsWithoutApproval();
        switch (permission) {
            case DEFAULT -> {
                disabled.remove(toolName);
                with.remove(toolName);
                without.remove(toolName);
            }
            case WITH_APPROVAL -> {
                with.add(toolName);
                disabled.remove(toolName);
                without.remove(toolName);
            }
            case WITHOUT_APPROVAL -> {
                without.add(toolName);
                with.remove(toolName);
                disabled.remove(toolName);
            }
            case DISABLED -> {
                disabled.add(toolName);
                with.remove(toolName);
                without.remove(toolName);
            }
        }
    }

    /** The working copy of the settings edited by this panel. */
    public LlmSettings getModel() {
        return model;
    }
}
