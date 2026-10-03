/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import java.awt.*;
import java.util.ArrayList;
import javax.swing.*;

import org.key_project.key.llm.mcp.BuiltInMCPClient;

import org.jspecify.annotations.Nullable;

/**
 * Dialogs to create and edit user-defined prompts and skills. The results are persisted by the
 * file-backed {@link PromptLibrary} / {@link SkillLibrary}.
 *
 * @author Alexander Weigl
 */
public final class LlmLibraryDialogs {
    private LlmLibraryDialogs() {
    }

    /**
     * Shows the prompt editor. A newly created prompt that is valid is stored in
     * {@link PromptLibrary}.
     *
     * @param parent the owner window
     * @param initialName prefilled name (for replacement) or {@code null}
     * @param initialTemplate prefilled template (e.g. the current input) or {@code null}
     */
    public static void showPromptDialog(Component parent, @Nullable String initialName,
            @Nullable String initialTemplate) {
        var name = new JTextField(initialName == null ? "" : initialName, 30);
        var description = new JTextField(30);
        var template = new JTextArea(initialTemplate == null ? "" : initialTemplate, 10, 40);
        template.setLineWrap(true);
        template.setWrapStyleWord(true);

        var panel = new JPanel(new GridBagLayout());
        var gbc = new GridBagConstraints();
        gbc.gridx = 0;
        gbc.gridy = 0;
        gbc.anchor = GridBagConstraints.WEST;
        gbc.insets = new Insets(4, 4, 4, 4);
        panel.add(new JLabel("Name (letters, digits, '_', '-'):"), gbc);
        gbc.gridx = 1;
        gbc.fill = GridBagConstraints.HORIZONTAL;
        gbc.weightx = 1;
        panel.add(name, gbc);
        gbc.gridx = 0;
        gbc.gridy = 1;
        gbc.fill = GridBagConstraints.NONE;
        gbc.weightx = 0;
        panel.add(new JLabel("Description:"), gbc);
        gbc.gridx = 1;
        gbc.fill = GridBagConstraints.HORIZONTAL;
        gbc.weightx = 1;
        panel.add(description, gbc);
        gbc.gridx = 0;
        gbc.gridy = 2;
        gbc.fill = GridBagConstraints.NONE;
        gbc.weightx = 0;
        panel.add(new JLabel("Template:"), gbc);
        gbc.gridx = 1;
        gbc.gridy = 2;
        gbc.fill = GridBagConstraints.BOTH;
        gbc.weighty = 1;
        panel.add(new JScrollPane(template), gbc);

        int ok = JOptionPane.showConfirmDialog(parent, panel, "Edit prompt",
            JOptionPane.OK_CANCEL_OPTION, JOptionPane.PLAIN_MESSAGE);
        if (ok != JOptionPane.OK_OPTION) {
            return;
        }
        var prompt = new Prompt(name.getText(), description.getText().strip(), template.getText());
        var error = PromptLibrary.INSTANCE.save(prompt);
        if (error != null) {
            JOptionPane.showMessageDialog(parent, error, "Could not save prompt",
                JOptionPane.ERROR_MESSAGE);
        }
    }

    /** Shows the skill editor and stores a valid result in {@link SkillLibrary}. */
    public static void showSkillDialog(Component parent, @Nullable Skill existing) {
        var name = new JTextField(existing == null ? "" : existing.name(), 30);
        var description = new JTextField(existing == null ? "" : existing.description(), 30);
        var instructions = new JTextArea(existing == null ? "" : existing.instructions(), 8, 40);
        instructions.setLineWrap(true);
        instructions.setWrapStyleWord(true);

        var knownTools = new BuiltInMCPClient().getAllToolNames();
        var allowedTools = new JList<>(knownTools.toArray(new String[0]));
        allowedTools.setVisibleRowCount(4);
        if (existing != null) {
            var sel = new java.util.HashSet<>(existing.allowedTools());
            var model = allowedTools.getModel();
            for (int i = 0; i < model.getSize(); i++) {
                if (sel.contains(model.getElementAt(i))) {
                    allowedTools.getSelectionModel().addSelectionInterval(i, i);
                }
            }
        }
        var enabled = new JCheckBox("enabled", existing == null || existing.enabled());

        var panel = new JPanel(new GridBagLayout());
        var gbc = new GridBagConstraints();
        gbc.gridx = 0;
        gbc.gridy = 0;
        gbc.anchor = GridBagConstraints.WEST;
        gbc.insets = new Insets(4, 4, 4, 4);
        panel.add(new JLabel("Name:"), gbc);
        gbc.gridx = 1;
        gbc.fill = GridBagConstraints.HORIZONTAL;
        gbc.weightx = 1;
        panel.add(name, gbc);
        gbc.gridx = 0;
        gbc.gridy = 1;
        gbc.fill = GridBagConstraints.NONE;
        gbc.weightx = 0;
        panel.add(new JLabel("Description:"), gbc);
        gbc.gridx = 1;
        gbc.fill = GridBagConstraints.HORIZONTAL;
        gbc.weightx = 1;
        panel.add(description, gbc);
        gbc.gridx = 0;
        gbc.gridy = 2;
        gbc.fill = GridBagConstraints.NONE;
        gbc.weightx = 0;
        panel.add(new JLabel("Instructions:"), gbc);
        gbc.gridx = 1;
        gbc.gridy = 2;
        gbc.fill = GridBagConstraints.BOTH;
        gbc.weighty = 1;
        panel.add(new JScrollPane(instructions), gbc);
        gbc.gridx = 0;
        gbc.gridy = 3;
        gbc.weightx = 0;
        gbc.weighty = 0;
        gbc.fill = GridBagConstraints.NONE;
        panel.add(new JLabel("Allowed tools (empty = no restriction):"), gbc);
        gbc.gridx = 1;
        gbc.fill = GridBagConstraints.BOTH;
        panel.add(new JScrollPane(allowedTools), gbc);
        gbc.gridx = 1;
        gbc.gridy = 4;
        gbc.fill = GridBagConstraints.NONE;
        panel.add(enabled, gbc);

        int ok = JOptionPane.showConfirmDialog(parent, panel, "Edit skill",
            JOptionPane.OK_CANCEL_OPTION, JOptionPane.PLAIN_MESSAGE);
        if (ok != JOptionPane.OK_OPTION) {
            return;
        }
        var allowed = new ArrayList<>(allowedTools.getSelectedValuesList());
        var skill = new Skill(name.getText(), description.getText().strip(),
            instructions.getText(), allowed, enabled.isSelected());
        var error = SkillLibrary.INSTANCE.save(skill);
        if (error != null) {
            JOptionPane.showMessageDialog(parent, error, "Could not save skill",
                JOptionPane.ERROR_MESSAGE);
        }
    }
}
