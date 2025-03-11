/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching.settings;

import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import net.miginfocom.layout.CC;

import static de.uka.ilkd.key.gui.plugins.caching.settings.ProofCachingSettings.DISPOSE_COPY;
import static de.uka.ilkd.key.gui.plugins.caching.settings.ProofCachingSettings.DISPOSE_REOPEN;
import static de.uka.ilkd.key.gui.plugins.caching.settings.ProofCachingSettings.PRUNE_COPY;
import static de.uka.ilkd.key.gui.plugins.caching.settings.ProofCachingSettings.PRUNE_REOPEN;

/**
 * Settings for the proof caching extension.
 *
 * @author Arne Keller
 */
public class CachingSettingsProvider extends SettingsPanel implements SettingsProvider {
    /**
     * Singleton instance of the caching settings.
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
     * Label for second option.
     */
    private static final String DISPOSE_TITLE =
        "Behaviour when disposing referenced proof";
    /**
     * Label for third option.
     */
    private static final String PRUNE_TITLE =
        "Behaviour when pruning into referenced proof";

    /**
     * Checkbox for first option.
     */
    private final JCheckBox strategySearch;
    /**
     * Combobox for second option (dispose behaviour).
     */
    private final JComboBox<String> disposeOption;
    /**
     * Combobox for third option (prune behaviour).
     */
    private final JComboBox<String> pruneOption;

    /**
     * Construct a new settings provider.
     */
    public CachingSettingsProvider() {
        setHeaderText("Proof Caching Options");

        pCenter.add(new JLabel(INTRO_LABEL), new CC().span().alignX("left"));

        strategySearch =
            addCheckBox(STRATEGY_SEARCH, "", true, emptyValidator());
        disposeOption = addComboBox(DISPOSE_TITLE, """
                When a referenced proof is disposed, this is what happens to
                 all cached branches that reference it.""",
            0, x -> {
            }, DISPOSE_COPY, DISPOSE_REOPEN);
        pruneOption = addComboBox(PRUNE_TITLE, """
                When a referenced proof is pruned, this is what happens to
                 all cached branches that reference it.""",
            0, x -> {
            }, PRUNE_REOPEN, PRUNE_COPY);
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
    public JPanel getPanel(MainWindow window) {
        ProofCachingSettings ss = getCachingSettings();
        strategySearch.setSelected(ss.getEnabled());
        disposeOption.setSelectedItem(ss.getDispose());
        pruneOption.setSelectedItem(ss.getPrune());
        return this;
    }

    @Override
    public void applySettings(MainWindow window) {
        ProofCachingSettings ss = getCachingSettings();
        ss.setEnabled(strategySearch.isEnabled());
        ss.setDispose(disposeOption.getSelectedItem().toString());
        ss.setPrune(pruneOption.getSelectedItem().toString());
    }


    @Override
    public int getPriorityOfSettings() {
        return 10000;
    }
}
