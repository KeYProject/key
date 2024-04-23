/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing;


import java.util.ArrayList;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.gui.utilities.FormDialog;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.key_project.util.collection.Pair;

import net.miginfocom.layout.CC;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Settings for the proof slicing extension.
 *
 * @author Arne Keller
 */
public class ProofRegroupSettingsProvider extends SettingsPanel implements SettingsProvider {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(ProofRegroupSettingsProvider.class);

    /**
     * Singleton instance of the settings.
     */
    private static final ProofRegroupSettings SETTINGS = new ProofRegroupSettings();

    /**
     * Text for introductory explanation
     */
    private static final String INTRO_LABEL = "Adjust heuristics groups here.";

    /**
     * The configured groups: name -> text area with heuristic names.
     */
    private final List<Pair<String, JTextArea>> groups = new ArrayList<>();

    /**
     * Construct a new settings provider.
     */
    public ProofRegroupSettingsProvider() {
        setHeaderText("Proof Regrouping Options");
    }

    @Override
    public String getDescription() {
        return "Proof Regrouping";
    }

    /**
     * @return the settings managed by this provider
     */
    public static ProofRegroupSettings getSettings() {
        ProofIndependentSettings.DEFAULT_INSTANCE.addSettings(SETTINGS);
        return SETTINGS;
    }

    @Override
    public JPanel getPanel(MainWindow window) {
        return getPanel(window, null);
    }

    @Override
    public JPanel getPanel(MainWindow window, JDialog dialog) {
        ProofRegroupSettings ss = getSettings();

        pCenter.removeAll();
        pCenter.add(new JLabel(INTRO_LABEL), new CC().span().alignX("left"));

        for (var e : ss.getGroups().entrySet()) {
            var ta =
                addTextArea(e.getKey(), String.join("\n", e.getValue()), null, emptyValidator());
            groups.add(new Pair<>(e.getKey(), ta));
        }

        setupAddAndRemoveButtons(dialog, ss);

        return this;
    }

    private void setupAddAndRemoveButtons(JDialog dialog, ProofRegroupSettings ss) {
        // remove any previously added buttons
        for (int i = 0; i < pCenter.getComponentCount(); i++) {
            if (pCenter.getComponent(i) instanceof JButton) {
                pCenter.remove(i);
                i--;
            }
        }

        var addNew = new JButton("Add new group");
        addNew.addActionListener(e -> {
            try {
                new FormDialog(dialog, "Add new group",
                    List.of(new FormDialog.NamedInputElement("Name", new JTextField()),
                        new FormDialog.NamedInputElement("Heuristics", new JTextArea())),
                    data -> {
                        var name = data.get("Name");
                        if (ss.getGroups().containsKey(name)) {
                            return "Group name already in use!";
                        }
                        return null;
                    },
                    data -> {
                        var name = data.get("Name");
                        var content = data.get("Heuristics");
                        var ta =
                            addTextArea(name, "", null, emptyValidator());
                        ta.setText(content);
                        groups.add(new Pair<>(name, ta));
                        ss.addGroup(name, List.of(ta.getText().split("\n")));

                        setupAddAndRemoveButtons(dialog, ss);
                        dialog.validate();
                        dialog.repaint();
                    }, () -> {
                        // ignore cancel
                    });
            } catch (Exception err) {
                err.printStackTrace();
            }
        });
        pCenter.add(addNew, "wrap");
        for (var group : ss.getUserGroups().keySet()) {
            var remove = new JButton("Remove " + group);
            remove.addActionListener(e -> {
                try {
                    ss.removeGroup(group);
                    for (var groupPair : groups) {
                        if (groupPair.first.equals(group)) {
                            removeTitledComponent(groupPair.first);
                            groups.remove(groupPair);
                            setupAddAndRemoveButtons(dialog, ss);
                            dialog.validate();
                            dialog.repaint();
                            break;
                        }
                    }
                } catch (Exception error) {
                    LOGGER.error("failed to remove group", error);
                }
            });
            pCenter.add(remove, "wrap");
        }
    }

    @Override
    public void applySettings(MainWindow window) {
        ProofRegroupSettings ss = getSettings();
        for (Pair<String, JTextArea> ta : groups) {
            ss.updateGroup(ta.first, List.of(ta.second.getText().split("\n")));
        }
    }


    @Override
    public int getPriorityOfSettings() {
        return 10000;
    }
}
