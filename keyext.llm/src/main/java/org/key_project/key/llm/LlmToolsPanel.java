/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.awt.FlowLayout;
import java.awt.Font;
import java.util.Collection;
import java.util.Comparator;
import java.util.EnumMap;
import javax.swing.*;

import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SimpleSettingsPanel;

import org.key_project.key.llm.mcp.BuiltInMCPClient;
import org.key_project.key.llm.mcp.Tool;
import org.key_project.key.llm.mcp.ToolCategory;

import net.miginfocom.layout.CC;

/**
 * Settings panel for the KeY-Agent tool permissions. It is shown as its own node ("Tools") under
 * "LLM Settings" in the settings dialog and edits a working copy of {@link LlmSettings}. Every tool
 * gets a block — the tool name on the left, its explanation flowing next to it, the permission
 * radio group and the background/export checkboxes below, separated by a horizontal line — the
 * tools are grouped and sorted by their {@link ToolCategory}. {@link #getModel()} hands the copy
 * to the settings provider for applying.
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
        this(model, new BuiltInMCPClient().getAllTools());
    }

    /**
     * Creates the panel for an explicit tool list. The public no-arg tool constructor fills the
     * list from the built-in registry; this variant injects the data shown in the rows and is used
     * by the UI-test harness (package {@code org.key_project.key.llm.uitest}) to drive the panel
     * with a small, deterministic mock tool set.
     *
     * @param model the working copy of the settings edited by this panel
     * @param tools the tools to show, one row each
     */
    public LlmToolsPanel(LlmSettings model, Collection<? extends Tool> tools) {
        this.model = model;

        setHeaderText("Tools");
        setSubHeaderText("Control which tools the KeY-Agent may call, whether they require"
            + " approval, whether they may run in the background and whether they are exported to"
            + " the MCP server. Disabled tools are not sent to the model at all.");

        var sorted = tools.stream()
                .sorted(Comparator.comparing((Tool t) -> t.category().ordinal())
                        .thenComparing(t -> t.function().name()))
                .toList();
        ToolCategory current = null;
        for (var tool : sorted) {
            if (tool.category() != current) {
                current = tool.category();
                addSeparator(current.label());
            } else {
                // a plain line between the tools of one category
                pCenter.add(new JSeparator(SwingConstants.HORIZONTAL),
                    new CC().span(3).growX().wrap());
            }
            addToolRow(tool);
        }
    }

    /**
     * Adds the block for one tool to the center grid: the (bold) tool name in the left column,
     * top-aligned with its flowing explanation, and below — spanning the full width — the
     * permission radio group and the background/export checkboxes on one line.
     */
    private void addToolRow(Tool tool) {
        var name = tool.function().name();

        var nameLabel = new JLabel(name);
        nameLabel.setFont(nameLabel.getFont().deriveFont(Font.BOLD));
        pCenter.add(nameLabel, new CC().alignY("top"));

        var description = toolDescription(tool.function().description());
        pCenter.add(description, new CC().growX().pushX().alignY("top"));

        var help = SimpleSettingsPanel.createHelpLabel(tool.function().description());
        pCenter.add(help, new CC().alignY("top").wrap());

        pCenter.add(radiosPanel(tool), new CC().span(3).growX().wrap());
        pCenter.add(checkboxesPanel(tool), new CC().span(3).growX().wrap());
    }

    /**
     * The flowing explanation of a tool. The column count caps the preferred width: a wrapping
     * JTextArea reports the width of its longest line as preferred size, which would inflate the
     * grid and prevent the text from flowing with the dialog width.
     */
    private static JTextArea toolDescription(String text) {
        var description = new JTextArea(text);
        description.setEditable(false);
        description.setFocusable(false);
        description.setOpaque(false);
        description.setLineWrap(true);
        description.setWrapStyleWord(true);
        description.setColumns(70);
        description.setBorder(BorderFactory.createEmptyBorder());
        description.setForeground(UIManager.getColor("Label.disabledForeground"));
        return description;
    }

    /**
     * The permission radio group of one tool (default, with approval, without approval, disabled).
     */
    private JPanel radiosPanel(Tool tool) {
        var name = tool.function().name();

        var defaultLabel = tool.defaultApproval() == Tool.ApprovalRequirement.ASK
                ? "Default (ask)"
                : "Default (auto)";
        var group = new ButtonGroup();
        var buttons = new EnumMap<Permission, JRadioButton>(Permission.class);
        buttons.put(Permission.DEFAULT, radio(group, defaultLabel));
        buttons.put(Permission.WITH_APPROVAL, radio(group, "With approval"));
        buttons.put(Permission.WITHOUT_APPROVAL, radio(group, "Without approval (always)"));
        buttons.put(Permission.DISABLED, radio(group, "Disabled"));

        buttons.get(currentPermission(name)).setSelected(true);
        for (var entry : buttons.entrySet()) {
            var permission = entry.getKey();
            entry.getValue().addActionListener(e -> applyPermission(name, permission));
        }

        var radios = new JPanel(new FlowLayout(FlowLayout.LEFT, 12, 0));
        for (var button : buttons.values()) {
            radios.add(button);
        }
        return radios;
    }

    /** The "may run in background" and "export to MCP" checkboxes of one tool, on one line. */
    private JPanel checkboxesPanel(Tool tool) {
        var name = tool.function().name();

        var background = new JCheckBox("may run in background");
        background.setSelected(model.isBackgroundAllowed(name, tool.backgroundable()));
        background.setToolTipText("While such a call is running it can be moved to the"
            + " background; the agent then continues with your queued messages and the result is"
            + " delivered when the call finishes.");
        background.addActionListener(e -> applyBackground(name, background.isSelected()));

        var export = new JCheckBox("export to MCP");
        boolean defaultExport = model.isExportedToMCPByDefault(name,
            tool.defaultApproval() == Tool.ApprovalRequirement.AUTO);
        export.setSelected(model.isExportedToMCP(name, defaultExport));
        export.setToolTipText("Expose this tool to external processes over the MCP server"
            + " (SSE). By default the auto-approved tools are exported; an explicit choice"
            + " overrides that default.");
        export.addActionListener(e -> applyExport(name, export.isSelected()));

        var checkboxes = new JPanel(new FlowLayout(FlowLayout.LEFT, 12, 0));
        checkboxes.add(background);
        checkboxes.add(export);
        return checkboxes;
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

    /**
     * Writes the chosen background permission into the (mutually exclusive) tool sets of the
     * working copy: checked means "may run in background", unchecked (after an explicit toggle)
     * "must not run in the background".
     */
    private void applyBackground(String toolName, boolean allowed) {
        var enabled = model.getBackgroundToolsEnabled();
        var disabled = model.getBackgroundToolsDisabled();
        if (allowed) {
            enabled.add(toolName);
            disabled.remove(toolName);
        } else {
            disabled.add(toolName);
            enabled.remove(toolName);
        }
    }

    /**
     * Writes the chosen MCP export permission into the (mutually exclusive) override sets of the
     * working copy: checked means "always exported", unchecked "never exported". Without an
     * explicit choice the tool follows its metadata default (shown as the initial state).
     */
    private void applyExport(String toolName, boolean exported) {
        var exportedSet = model.getMcpExportedTools();
        var notExportedSet = model.getMcpNotExportedTools();
        if (exported) {
            exportedSet.add(toolName);
            notExportedSet.remove(toolName);
        } else {
            notExportedSet.add(toolName);
            exportedSet.remove(toolName);
        }
    }

    /** The working copy of the settings edited by this panel. */
    public LlmSettings getModel() {
        return model;
    }
}
