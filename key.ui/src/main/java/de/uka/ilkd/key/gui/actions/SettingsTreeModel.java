/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.util.Collection;
import java.util.Map;
import javax.swing.*;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.MutableTreeNode;

import de.uka.ilkd.key.gui.smt.OptionContentNode;
import de.uka.ilkd.key.settings.*;

import org.key_project.logic.Choice;

/**
 * A swing model for {@link ShowActiveSettingsAction}.
 *
 * @author Mihai Herda, 2018
 */

public class SettingsTreeModel extends DefaultTreeModel {
    private final ProofSettings proofSettings;
    private final ProofIndependentSettings independentSettings;
    private DefaultMutableTreeNode tacletOptionsItem;

    public SettingsTreeModel(ProofSettings proofSettings,
            ProofIndependentSettings independentSettings) {
        super(new DefaultMutableTreeNode("All Settings"));

        this.proofSettings = proofSettings;
        this.independentSettings = independentSettings;

        generateTree();
    }

    private void generateTree() {
        DefaultMutableTreeNode root = new DefaultMutableTreeNode("All Settings");

        if (proofSettings == null) {
            OptionContentNode proofSettingsNode =
                generateOptionContentNode("Proof Settings", "There is currently no proof loaded!");
            root.add(proofSettingsNode);
        } else {
            OptionContentNode proofSettingsNode =
                generateOptionContentNode("Proof Settings",
                    "These are the proof dependent settings.");
            root.add(proofSettingsNode);

            configurationTable(proofSettingsNode, proofSettings.asConfiguration());
        }

        var independentSettingsNode = generateOptionContentNode(
            "Proof-Independent Settings", "These are the proof independent settings.");
        root.add(independentSettingsNode);
        configurationTable(independentSettingsNode, independentSettings.asConfiguration());

        setRoot(root);
    }


    public JComponent getStartComponent() {
        return generateScrollPane("Here are all settings.");
    }

    private MutableTreeNode generateTableNode(String title, Settings settings) {
        Configuration c = new Configuration();
        settings.writeSettings(c);
        var n = new DefaultMutableTreeNode(title);
        configurationTable(n, c);
        return n;
    }

    private DefaultMutableTreeNode generateTableNode(String title, ChoiceSettings settings) {
        Configuration c = new Configuration();
        settings.writeSettings(c);
        var node = new DefaultMutableTreeNode(title);
        configurationTable(node, c);
        return node;
    }


    private JComponent generateScrollPane(String text) {
        JTextArea ta = new JTextArea(5, 20);
        ta.append(text);
        ta.setEditable(false);
        ta.setBorder(BorderFactory.createEmptyBorder(10, 10, 10, 10));
        return new JScrollPane(ta);
    }

    private void configurationTable(DefaultMutableTreeNode parent, Object value) {
        if (value == null) {
            parent.add(new DefaultMutableTreeNode(" <not set>"));
        } else if (value instanceof String || value instanceof Long || value instanceof Integer
                || value instanceof Double || value instanceof Float
                || value instanceof Short || value instanceof Byte
                || value instanceof Boolean || value instanceof Enum<?>) {
            parent.add(new DefaultMutableTreeNode(value));
        } else if (value instanceof Collection<?> col) {
            configurationTable(parent, col);
        } else if (value instanceof Map map) {
        } else if (value instanceof Configuration map) {
            configurationTable(parent, map);
        }
    }

    private void configurationTable(DefaultMutableTreeNode parent, Configuration value) {
        var names = value.getKeys().stream().sorted().toList();

        for (String name : names) {
            var v = value.get(name);

            if (v instanceof Collection || v instanceof Map || v instanceof Configuration) {
                var newChild = new DefaultMutableTreeNode(name);
                parent.add(newChild);
                configurationTable(newChild, v);
            } else {
                parent.add(new DefaultMutableTreeNode(name + ": " + v));
            }
        }
    }

    private void configurationTable(DefaultMutableTreeNode parent, Collection<?> values) {
        for (var value : values) {
            configurationTable(parent, value);
        }
    }


    private OptionContentNode generateOptionContentNode(String title, String text) {
        return new OptionContentNode(title, generateScrollPane(text));
    }

    public DefaultMutableTreeNode getTacletOptionsItem() {
        return tacletOptionsItem;
    }
}
