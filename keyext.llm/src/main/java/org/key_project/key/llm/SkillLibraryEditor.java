/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.awt.Dimension;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import javax.swing.*;

import de.uka.ilkd.key.gui.settings.SettingsPanel;

import org.key_project.key.llm.mcp.BuiltInMCPClient;

import org.jspecify.annotations.Nullable;

/**
 * Embedded editor for the user-defined skills ({@link SkillLibrary}) shown in the LLM settings
 * panel. The form follows the usual KeY settings layout: label, input and help icon per row; the
 * allowed-tools whitelist is a list of checkboxes.
 *
 * @author Alexander Weigl
 */
public class SkillLibraryEditor extends LibraryEditorPanel<Skill> {
    /** Explanations shown as help icons behind the form fields. */
    static final String HELP_NAME =
        "A unique short identifier (letters, digits, '_', '-'). It is also the file name and the"
            + " trigger for /skill:NAME.";
    static final String HELP_DESCRIPTION =
        "A short summary shown in the chat (/skills) and to the agent.";
    static final String HELP_INSTRUCTIONS =
        "Instructions appended to the system prompt while the skill is active. They may reference"
            + " tokens such as $seq or $goals.";
    static final String HELP_ALLOWED_TOOLS =
        "Optional whitelist: while the skill is active the agent may only call these tools. If no"
            + " tool is selected, every enabled tool stays available.";
    static final String HELP_ENABLED =
        "Whether the skill can be selected and stays active. Disabled skills are ignored by the"
            + " agent.";

    private final JTextArea instructions = new JTextArea(6, 50);
    private final List<JCheckBox> toolChecks = new ArrayList<>();
    private final JCheckBox enabled = new JCheckBox("Enabled");

    public SkillLibraryEditor() {
        super("Skills",
            "A skill adds focused instructions and an optional tool whitelist to the agent's system"
                + " prompt. Changes are saved immediately.");
        instructions.setLineWrap(true);
        instructions.setWrapStyleWord(true);

        var toolBox = new JPanel();
        toolBox.setLayout(new BoxLayout(toolBox, BoxLayout.Y_AXIS));
        for (var name : new BuiltInMCPClient().getAllToolNames()) {
            var check = new JCheckBox(name);
            toolChecks.add(check);
            toolBox.add(check);
        }
        var toolsScroll = new JScrollPane(toolBox);
        toolsScroll.setPreferredSize(new Dimension(240, 120));

        setForm(buildForm(toolsScroll));
        reload();
    }

    private JComponent buildForm(JComponent toolsScroll) {
        return new SettingsPanel() {
            {
                addTitledComponent("Name", txtName, HELP_NAME);
                addTitledComponent("Description", txtDescription, HELP_DESCRIPTION);
                addTitledComponent("Instructions", new JScrollPane(instructions),
                    HELP_INSTRUCTIONS);
                addTitledComponent("Allowed tools", toolsScroll, HELP_ALLOWED_TOOLS);
                addRowWithHelp(HELP_ENABLED, new JLabel(), enabled);
            }
        };
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
        Set<String> selected = e == null ? Set.of() : new HashSet<>(e.allowedTools());
        for (var check : toolChecks) {
            check.setSelected(selected.contains(check.getText()));
        }
        enabled.setSelected(e == null || e.enabled());
    }

    @Override
    protected Skill formData() {
        List<String> allowed =
            toolChecks.stream().filter(AbstractButton::isSelected).map(JCheckBox::getText).toList();
        return new Skill(txtName.getText(), txtDescription.getText().strip(),
            instructions.getText(), allowed, enabled.isSelected());
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
