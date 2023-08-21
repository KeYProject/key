/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing;

import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import net.miginfocom.layout.CC;

/**
 * Settings for the proof slicing extension.
 *
 * @author Arne Keller
 */
public class SlicingSettingsProvider extends SettingsPanel implements SettingsProvider {
    /**
     * Singleton instance of the slicing settings.
     */
    private static final SlicingSettings SLICING_SETTINGS = new SlicingSettings();

    /**
     * Text for introductory explanation
     */
    private static final String INTRO_LABEL = "Adjust proof analysis algorithm options here.";
    /**
     * Label for first option.
     */
    private static final String AGGRESSIVE_DEDUPLICATE = "Aggressive rule de-duplication";
    /**
     * Explanatory text for first option.
     */
    private static final String AGGRESSIVE_DEDUPLICATE_INFO =
        "If enabled, the analysis algorithm will de-duplicate more than one duplicate pair"
            + " at once.\nThis may attempt to combine duplicates in impossible ways."
            + "\nDisable if you're having trouble slicing a proof using the de-duplication"
            + " algorithm.";
    private static final String DOT_EXECUTABLE = "Graphviz dot executable";
    private static final String DOT_EXECUTABLE_INFO =
        "Path to dot executable from the graphviz package.";

    /**
     * Checkbox for first option.
     */
    private final JCheckBox aggressiveDeduplicate;
    private final JTextField dotExecutable;

    /**
     * Construct a new settings provider.
     */
    public SlicingSettingsProvider() {
        setHeaderText("Proof Slicing Options");

        pCenter.add(new JLabel(INTRO_LABEL), new CC().span().alignX("left"));

        addSeparator("Dependency graph");
        dotExecutable = addTextField(DOT_EXECUTABLE, "dot", DOT_EXECUTABLE_INFO, e -> {
        });

        addSeparator("Duplicate rule applications");
        aggressiveDeduplicate =
            addCheckBox(AGGRESSIVE_DEDUPLICATE, AGGRESSIVE_DEDUPLICATE_INFO, true, e -> {
            });
    }

    @Override
    public String getDescription() {
        return "Proof Slicing";
    }

    /**
     * @return the settings managed by this provider
     */
    public static SlicingSettings getSlicingSettings() {
        ProofIndependentSettings.DEFAULT_INSTANCE.addSettings(SLICING_SETTINGS);
        return SLICING_SETTINGS;
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        SlicingSettings ss = getSlicingSettings();
        dotExecutable.setText(ss.getDotExecutable());
        aggressiveDeduplicate.setSelected(ss.getAggressiveDeduplicate(null));
        return this;
    }

    @Override
    public void applySettings(MainWindow window) {
        SlicingSettings ss = getSlicingSettings();
        ss.setDotExecutable(dotExecutable.getText());
        ss.setAggressiveDeduplicate(aggressiveDeduplicate.isSelected());
    }


    @Override
    public int getPriorityOfSettings() {
        return 10000;
    }
}
