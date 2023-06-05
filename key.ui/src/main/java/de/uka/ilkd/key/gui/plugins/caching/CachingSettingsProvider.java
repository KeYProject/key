package de.uka.ilkd.key.gui.plugins.caching;

import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.ProofCachingSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import net.miginfocom.layout.CC;

/**
 * Settings for the proof slicing extension.
 *
 * @author Arne Keller
 */
public class CachingSettingsProvider extends SettingsPanel implements SettingsProvider {
    /**
     * Singleton instance of the slicing settings.
     */
    private static final ProofCachingSettings CACHING_SETTINGS = new ProofCachingSettings();

    /**
     * Text for introductory explanation
     */
    private static final String INTRO_LABEL = "Adjust proof caching algorithm options here.";
    /**
     * Label for first option.
     */
    private static final String STRATEGY_SEARCH =
        "Automatically search for references in auto mode";
    /**
     * Explanatory text for first option.
     */
    private static final String AGGRESSIVE_DEDUPLICATE_INFO =
        "If enabled, the caching algorithm will run after every branching proof step created"
            + " by the autopilot. When a reference is found, that branch is marked and "
            + "the autopilot continues with the next open goal.";

    /**
     * Checkbox for first option.
     */
    private final JCheckBox strategySearch;

    /**
     * Construct a new settings provider.
     */
    public CachingSettingsProvider() {
        setHeaderText("Proof Caching Options");

        pCenter.add(new JLabel(INTRO_LABEL), new CC().span().alignX("left"));

        strategySearch =
            addCheckBox(STRATEGY_SEARCH, "", true, emptyValidator());
    }

    @Override
    public String getDescription() {
        return "Proof Caching";
    }

    /**
     * @return the settings managed by this provider
     */
    public static ProofCachingSettings getCachingSettings() {
        ProofIndependentSettings.DEFAULT_INSTANCE.addSettings(CACHING_SETTINGS);
        return CACHING_SETTINGS;
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        ProofCachingSettings ss = getCachingSettings();
        strategySearch.setSelected(ss.getEnabled());
        return this;
    }

    @Override
    public void applySettings(MainWindow window) {
        ProofCachingSettings ss = getCachingSettings();
        ss.setEnabled(strategySearch.isEnabled());
    }


    @Override
    public int getPriorityOfSettings() {
        return 10000;
    }
}
