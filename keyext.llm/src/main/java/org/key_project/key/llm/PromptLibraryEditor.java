/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.util.List;
import javax.swing.*;

import org.jspecify.annotations.Nullable;

/**
 * Embedded editor for the user-defined prompts ({@link PromptLibrary}) shown in the LLM settings
 * panel.
 *
 * @author Alexander Weigl
 */
public class PromptLibraryEditor extends LibraryEditorPanel<Prompt> {
    private final JTextArea template = new JTextArea(8, 50);

    public PromptLibraryEditor() {
        super();
        template.setLineWrap(true);
        template.setWrapStyleWord(true);
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
        form.add(new JLabel("Template:"), gbc);
        gbc.gridx = 1;
        gbc.gridy = 2;
        gbc.fill = GridBagConstraints.BOTH;
        gbc.weighty = 1;
        form.add(new JScrollPane(template), gbc);
        return form;
    }

    @Override
    protected List<Prompt> loadAll() {
        return PromptLibrary.INSTANCE.all();
    }

    @Override
    protected String nameOf(Prompt e) {
        return e.name();
    }

    @Override
    protected String descriptionOf(Prompt e) {
        return e.description();
    }

    @Override
    protected void populateForm(@Nullable Prompt e) {
        txtName.setText(e == null ? "" : e.name());
        txtDescription.setText(e == null ? "" : e.description());
        template.setText(e == null ? "" : e.template());
    }

    @Override
    protected Prompt formData() {
        return new Prompt(txtName.getText(), txtDescription.getText().strip(), template.getText());
    }

    @Override
    protected String store(Prompt e) {
        return PromptLibrary.INSTANCE.save(e);
    }

    @Override
    protected String removeByName(String name) {
        return PromptLibrary.INSTANCE.delete(name);
    }
}
