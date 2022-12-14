package org.key_project.slicing;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import net.miginfocom.layout.CC;

import javax.swing.*;

/**
 * Settings for the proof slicing extension.
 *
 * @author Arne Keller
 */
public class SlicingSettingsProvider extends SettingsPanel implements SettingsProvider {
    private static final SlicingSettings SLICING_SETTINGS = new SlicingSettings();

    /**
     * Text for introductory explanation
     */
    private static final String INTRO_LABEL = "Adjust proof analysis algorithm options here.";
    private static final String AGGRESSIVE_DEDUPLICATE = "Aggressive rule de-duplication";
    private static final String AGGRESSIVE_DEDUPLICATE_INFO =
        "If enabled, the analysis algorithm will de-duplicate more than one duplicate pair"
            + " at once.\nThis may attempt to combine duplicates in impossible ways."
            + "\nDisable if you're having trouble slicing a proof using the de-duplication"
            + " algorithm.";
    private final JCheckBox aggressiveDeduplicate;

    public SlicingSettingsProvider() {
        setHeaderText("Proof Slicing Options");

        pCenter.add(new JLabel(INTRO_LABEL), new CC().span().alignX("left"));

        addSeparator("Duplicate rule applications");
        aggressiveDeduplicate =
            addCheckBox(AGGRESSIVE_DEDUPLICATE, AGGRESSIVE_DEDUPLICATE_INFO, true, e -> {
            });
    }

    @Override
    public String getDescription() {
        return "Proof Slicing";
    }

    public static SlicingSettings getSlicingSettings() {
        ProofIndependentSettings.DEFAULT_INSTANCE.addSettings(SLICING_SETTINGS);
        return SLICING_SETTINGS;
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        SlicingSettings ss = getSlicingSettings();
        aggressiveDeduplicate.setSelected(ss.getAggressiveDeduplicate());
        return this;
    }

    @Override
    public void applySettings(MainWindow window) {
        SlicingSettings ss = getSlicingSettings();
        ss.setAggressiveDeduplicate(aggressiveDeduplicate.isSelected());
    }


    @Override
    public int getPriorityOfSettings() {
        return 10000;
    }
}

