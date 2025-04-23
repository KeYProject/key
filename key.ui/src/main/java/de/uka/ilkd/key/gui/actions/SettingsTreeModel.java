/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.util.Arrays;
import java.util.Map.Entry;
import java.util.Properties;
import javax.swing.*;
import javax.swing.table.DefaultTableModel;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;

import de.uka.ilkd.key.gui.smt.OptionContentNode;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.settings.Settings;

import org.key_project.logic.Choice;

/**
 *
 * A swing model for {@link ShowActiveSettingsAction}.
 *
 * @author Mihai Herda, 2018
 */

public class SettingsTreeModel extends DefaultTreeModel {

    private static final long serialVersionUID = -3282304543262262159L;

    private final ProofSettings proofSettings;

    private final ProofIndependentSettings independentSettings;
    private OptionContentNode tacletOptionsItem;

    public SettingsTreeModel(ProofSettings proofSettings,
            ProofIndependentSettings independentSettings) {
        super(new DefaultMutableTreeNode("All Settings"));
        this.proofSettings = proofSettings;
        this.independentSettings = independentSettings;
        generateTree();
    }

    private void generateTree() {
        DefaultMutableTreeNode root = (DefaultMutableTreeNode) this.getRoot();

        if (proofSettings == null) {
            OptionContentNode proofSettingsNode =
                generateOptionContentNode("Proof Settings", "There is currently no proof loaded!");
            root.add(proofSettingsNode);
        } else {
            OptionContentNode proofSettingsNode =
                generateOptionContentNode("Proof Settings",
                    "These are the proof dependent settings.");
            root.add(proofSettingsNode);

            // ChoiceSettings choiceSettings = proofSettings.getChoiceSettings();
            ChoiceSettings choiceSettings = proofSettings.getChoiceSettings();
            tacletOptionsItem = generateTableNode("Taclet Options", choiceSettings);
            proofSettingsNode.add(tacletOptionsItem);

            Settings strategySettings = proofSettings.getStrategySettings();
            proofSettingsNode.add(generateTableNode("Strategy", strategySettings));

            Settings smtSettings = proofSettings.getSMTSettings();
            proofSettingsNode.add(generateTableNode("SMT", smtSettings));
        }

        OptionContentNode independentSettingsNode = generateOptionContentNode(
            "Proof-Independent Settings", "These are the proof independent settings.");
        root.add(independentSettingsNode);

        Settings generalSettings = independentSettings.getGeneralSettings();
        independentSettingsNode.add(generateTableNode("General", generalSettings));
        Settings lemmaSettings = independentSettings.getLemmaGeneratorSettings();
        independentSettingsNode.add(generateTableNode("Lemma Generator", lemmaSettings));
        Settings indSMTSettings = independentSettings.getSMTSettings();
        independentSettingsNode.add(generateTableNode("SMT", indSMTSettings));
        // Settings testgenSettings =independentSettings.getTestGenerationSettings();
        // independentSettingsNode.add(generateTableNode("Testcase Generation", testgenSettings));
        Settings viewSettings = independentSettings.getViewSettings();
        independentSettingsNode.add(generateTableNode("View", viewSettings));
        Settings termLabelSettings = independentSettings.getTermLabelSettings();
        // Previously, the termLabelSettings were added to the proofSettingsNode, but judging by the
        // previous line,
        // it should really be added to the independentSettingsNode
        independentSettingsNode.add(generateTableNode("Term Labels", termLabelSettings));
    }



    public JComponent getStartComponent() {
        return generateScrollPane("Here are all settings.");
    }


    private Properties getChoicesAsProperties(ChoiceSettings settings) {
        Properties prop = new Properties();

        for (Choice choice : settings.getDefaultChoicesAsSet()) {
            prop.put(choice.category(), choice.name());
        }

        return prop;
    }

    private OptionContentNode generateTableNode(String title, Settings settings) {

        Properties props = new Properties();
        settings.writeSettings(props);

        return new OptionContentNode(title, generateJTable(props));

    }

    private OptionContentNode generateTableNode(String title, ChoiceSettings settings) {
        Properties props = getChoicesAsProperties(settings);
        return new OptionContentNode(title, generateJTable(props));

    }


    private JComponent generateScrollPane(String text) {
        JTextArea ta = new JTextArea(5, 20);
        ta.append(text);
        ta.setEditable(false);
        ta.setBorder(BorderFactory.createEmptyBorder(10, 10, 10, 10));
        JScrollPane scrollpane = new JScrollPane(ta);
        return scrollpane;
    }

    private JComponent generateJTable(Properties properties) {
        String[] columnNames = { "Name", "Value" };
        Object[][] data = new Object[properties.size()][2];

        int i = 0;
        for (Entry<Object, Object> entry : properties.entrySet()) {
            data[i][0] = entry.getKey();
            data[i][1] = entry.getValue();
            i++;
        }

        Arrays.sort(data, (a, b) -> a[0].toString().compareToIgnoreCase(b[0].toString()));

        JTable table = new JTable();

        DefaultTableModel tableModel = new DefaultTableModel() {
            private static final long serialVersionUID = 1L;

            @Override
            public boolean isCellEditable(int row, int column) {
                // all cells false
                return false;
            }
        };

        tableModel.setDataVector(data, columnNames);
        table.setModel(tableModel);
        table.setRowHeight(table.getRowHeight() + 10);

        JScrollPane scrollpane = new JScrollPane(table);
        return scrollpane;
    }



    private OptionContentNode generateOptionContentNode(String title, String text) {
        return new OptionContentNode(title, generateScrollPane(text));
    }

    public OptionContentNode getTacletOptionsItem() {
        return tacletOptionsItem;
    }
}
