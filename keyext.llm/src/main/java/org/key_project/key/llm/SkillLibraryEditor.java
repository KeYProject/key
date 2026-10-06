/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import javax.swing.*;

import org.key_project.key.llm.mcp.BuiltInMCPClient;

import org.jspecify.annotations.Nullable;

/**
 * Embedded editor for the user-defined skills ({@link SkillLibrary}) shown in the LLM settings
 * panel.
 *
 * @author Alexander Weigl
 */
public class SkillLibraryEditor extends LibraryEditorPanel<Skill> {
    private final JTextArea instructions = new JTextArea(6, 50);
    private final JList<String> allowedTools;
    private final JCheckBox enabled = new JCheckBox("enabled");

    public SkillLibraryEditor() {
        super();
        instructions.setLineWrap(true);
        instructions.setWrapStyleWord(true);
        allowedTools = new JList<>(new BuiltInMCPClient().getAllToolNames().toArray(new String[0]));
        allowedTools.setVisibleRowCount(4);
        setForm(buildForm());
        reload();
    }

    private JComponent buildForm() {
        var form = new JPanel(new GridBagLayout());
        var gbc = new GridBagConstraints();
        gbc.anchor = GridBagConstraints.WEST;
        gbc.insets = new Insets(4, 4, 4, 4);
        gbc.gridx = 0;
        gbc.gridy = 0;
        form.add(new JLabel("Name (letters, digits, '_', '-'):"), gbc);
        gbc.gridx = 1;
        gbc.fill = GridBagConstraints.HORIZONTAL;
        gbc.weightx = 1;
        form.add(txtName, gbc);
        gbc.gridx = 0;
        gbc.gridy = 1;
        gbc.fill = GridBagConstraints.NONE;
        gbc.weightx = 0;
        form.add(new JLabel("Description:"), gbc);
        gbc.gridx = 1;
        gbc.fill = GridBagConstraints.HORIZONTAL;
        gbc.weightx = 1;
        form.add(txtDescription, gbc);
        gbc.gridx = 0;
        gbc.gridy = 2;
        gbc.fill = GridBagConstraints.NONE;
        gbc.weightx = 0;
        form.add(new JLabel("Instructions:"), gbc);
        gbc.gridx = 1;
        gbc.gridy = 2;
        gbc.fill = GridBagConstraints.BOTH;
        gbc.weighty = 1;
        form.add(new JScrollPane(instructions), gbc);
        gbc.gridx = 0;
        gbc.gridy = 3;
        gbc.weightx = 0;
        gbc.weighty = 0;
        gbc.fill = GridBagConstraints.NONE;
        form.add(new JLabel("Allowed tools (empty = no restriction):"), gbc);
        gbc.gridx = 1;
        gbc.gridy = 3;
        gbc.fill = GridBagConstraints.BOTH;
        gbc.weighty = 1;
        form.add(new JScrollPane(allowedTools), gbc);
        gbc.gridx = 1;
        gbc.gridy = 4;
        gbc.fill = GridBagConstraints.NONE;
        gbc.weighty = 0;
        form.add(enabled, gbc);
        return form;
    }

    @Override
    protected List<Skill> loadAll() {
        return SkillLibrary.INSTANCE.all();
    }

    @Override
    protected String nameOf(Skill e) {
        return e.name();
    }

    @Override
    protected String descriptionOf(Skill e) {
        return e.description();
    }

    @Override
    protected void populateForm(@Nullable Skill e) {
        txtName.setText(e == null ? "" : e.name());
        txtDescription.setText(e == null ? "" : e.description());
        instructions.setText(e == null ? "" : e.instructions());
        allowedTools.clearSelection();
        if (e != null && !e.allowedTools().isEmpty()) {
            var selected = new HashSet<>(e.allowedTools());
            for (int i = 0; i < allowedTools.getModel().getSize(); i++) {
                if (selected.contains(allowedTools.getModel().getElementAt(i))) {
                    allowedTools.getSelectionModel().addSelectionInterval(i, i);
                }
            }
        }
        enabled.setSelected(e == null || e.enabled());
    }

    @Override
    protected Skill formData() {
        return new Skill(txtName.getText(), txtDescription.getText().strip(),
            instructions.getText(), new ArrayList<>(allowedTools.getSelectedValuesList()),
            enabled.isSelected());
    }

    @Override
    protected String store(Skill e) {
        return SkillLibrary.INSTANCE.save(e);
    }

    @Override
    protected String removeByName(String name) {
        return SkillLibrary.INSTANCE.delete(name);
    }
}
