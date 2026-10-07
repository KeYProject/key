/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.gui.settings.SettingsPanel;

import com.google.gson.GsonBuilder;
import com.google.gson.reflect.TypeToken;
import org.jspecify.annotations.Nullable;

/**
 * Embedded editor for the user-defined prompts ({@link PromptLibrary}) shown in the LLM settings
 * panel. The form follows the usual KeY settings layout: label, input and help icon per row.
 *
 * @author Alexander Weigl
 */
public class PromptLibraryEditor extends LibraryEditorPanel<Prompt> {
    /** Explanations shown as help icons behind the form fields. */
    static final String HELP_NAME =
        "A unique short identifier (letters, digits, '_', '-'). It is also the file name and the"
            + " trigger for /prompt:NAME.";
    static final String HELP_DESCRIPTION =
        "A short summary shown in the chat (/prompts).";
    static final String HELP_TEMPLATE =
        "The prompt text inserted into the chat when the prompt is used. Placeholders such as"
            + " $seq, $goals or file references @path are resolved at insertion time.";

    private final JTextArea template = new JTextArea(8, 50);

    public PromptLibraryEditor() {
        super("Prompts",
            "Reusable prompt templates for the chat; insert them with /prompt:NAME. Changes are"
                + " saved immediately.");
        template.setLineWrap(true);
        template.setWrapStyleWord(true);
        setFormComponent(buildForm());
        reload();
    }

    private JComponent buildForm() {
        return new SettingsPanel() {
            {
                // the form lives in its own dialog; no extra header here
                pNorth.setVisible(false);
                addTitledComponent("Name", txtName, HELP_NAME);
                addTitledComponent("Description", txtDescription, HELP_DESCRIPTION);
                addTitledComponent("Template", new JScrollPane(template), HELP_TEMPLATE);
            }
        };
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

    @Override
    protected String toJson(List<Prompt> entries) {
        return new GsonBuilder().setPrettyPrinting().create().toJson(entries);
    }

    @Override
    protected List<Prompt> fromJson(String json) {
        try {
            var type = new TypeToken<List<Prompt>>() {
            }.getType();
            List<Prompt> list = new GsonBuilder().create().fromJson(json, type);
            return list == null ? List.of() : list;
        } catch (Exception e) {
            return List.of();
        }
    }
}
