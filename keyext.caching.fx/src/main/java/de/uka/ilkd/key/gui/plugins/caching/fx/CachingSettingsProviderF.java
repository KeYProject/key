/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.plugins.caching.fx;

import javafx.scene.control.CheckBox;
import javafx.scene.control.ComboBox;
import javafx.scene.control.Label;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.settings.InvalidSettingsInputExceptionF;
import de.uka.ilkd.key.gui.fx.settings.SettingsPanelF;
import de.uka.ilkd.key.gui.fx.settings.SettingsProviderF;
import de.uka.ilkd.key.gui.plugins.caching.settings.ProofCachingSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import static de.uka.ilkd.key.gui.plugins.caching.settings.ProofCachingSettings.DISPOSE_COPY;
import static de.uka.ilkd.key.gui.plugins.caching.settings.ProofCachingSettings.DISPOSE_REOPEN;
import static de.uka.ilkd.key.gui.plugins.caching.settings.ProofCachingSettings.PRUNE_COPY;
import static de.uka.ilkd.key.gui.plugins.caching.settings.ProofCachingSettings.PRUNE_REOPEN;

/**
 * The "Proof Caching" options panel, FX port of {@code CachingSettingsProvider} (Swing
 * CachingSettingsProvider.java:26-121): the auto-search checkbox and the two behaviour combo
 * boxes (dispose / prune of referenced proofs), reading and writing the reused, persisted
 * {@link ProofCachingSettings}.
 *
 * @author Arne Keller (Swing original)
 * @author MP9.1 settings-panel port (FX)
 */
final class CachingSettingsProviderF extends SettingsPanelF implements SettingsProviderF {

    /**
     * Singleton instance of the caching settings (Swing
     * {@code CachingSettingsProvider.CACHING_SETTINGS}). OWNED by the FX module
     * (KNOWN-SIMPLIFIED: the Swing keyext {@code CachingSettingsProvider.getCachingSettings()}
     * is not loadable on the FX module's compile path — the key.ui interface behind it is not
     * exposed — so the FX module keeps the same {@code ProofCachingSettings} singleton and
     * registers it into the {@link ProofIndependentSettings} itself; the Swing extension and the
     * FX extension share the persisted object via that registry).
     */
    private static final ProofCachingSettings CACHING_SETTINGS = new ProofCachingSettings();

    static {
        ProofIndependentSettings.DEFAULT_INSTANCE.addSettings(CACHING_SETTINGS);
    }

    /** Text for the introductory explanation (Swing {@code INTRO_LABEL}). */
    private static final String INTRO_LABEL = "Adjust proof caching algorithm options here.";

    /** Label of the first option (Swing {@code STRATEGY_SEARCH}). */
    private static final String STRATEGY_SEARCH =
        "Automatically search for references in auto mode";

    /** Label of the second option (Swing {@code DISPOSE_TITLE}). */
    private static final String DISPOSE_TITLE = "Behaviour when disposing referenced proof";

    /** Label of the third option (Swing {@code PRUNE_TITLE}). */
    private static final String PRUNE_TITLE = "Behaviour when pruning into referenced proof";

    /** Checkbox for the first option (Swing {@code strategySearch}). */
    private final CheckBox strategySearch;

    /** Combo box for the second option — dispose behaviour (Swing {@code disposeOption}). */
    private final ComboBox<String> disposeOption;

    /** Combo box for the third option — prune behaviour (Swing {@code pruneOption}). */
    private final ComboBox<String> pruneOption;

    /**
     * Construct a new settings provider.
     */
    CachingSettingsProviderF() {
        setHeaderText("Proof Caching Options");

        Label intro = new Label(INTRO_LABEL);
        intro.setWrapText(true);
        pCenter.add(intro, 0, pCenter.getRowCount(), 3, 1);

        strategySearch = addCheckBox(STRATEGY_SEARCH, "", CACHING_SETTINGS.getEnabled());
        disposeOption = addComboBox(DISPOSE_TITLE, """
                When a referenced proof is disposed, this is what happens to
                 all cached branches that reference it.""",
            DISPOSE_COPY, DISPOSE_REOPEN);
        pruneOption = addComboBox(PRUNE_TITLE, """
                When a referenced proof is pruned, this is what happens to
                 all cached branches that reference it.""",
            PRUNE_COPY, PRUNE_REOPEN);
    }

    @Override
    public String getDescription() {
        return "Proof Caching";
    }

    @Override
    public javafx.scene.Node getPanel(MainWindowF window) {
        ProofCachingSettings ss = getCachingSettings();
        strategySearch.setSelected(ss.getEnabled());
        disposeOption.getSelectionModel().select(ss.getDispose());
        pruneOption.getSelectionModel().select(ss.getPrune());
        return this;
    }

    @Override
    public void apply(MainWindowF window) throws InvalidSettingsInputExceptionF {
        ProofCachingSettings ss = getCachingSettings();
        // KNOWN-SIMPLIFIED: the Swing original writes strategySearch.isEnabled() here
        // (CachingSettingsProvider.java:112 — JCheckBox#isEnabled, a latent bug that always
        // persisted true); the FX port writes the checkbox SELECTION, i.e. the behaviour the
        // panel visibly offers.
        ss.setEnabled(strategySearch.isSelected());
        String dispose = disposeOption.getSelectionModel().getSelectedItem();
        if (dispose != null) {
            ss.setDispose(dispose);
        }
        String prune = pruneOption.getSelectionModel().getSelectedItem();
        if (prune != null) {
            ss.setPrune(prune);
        }
    }

    /**
     * @return the settings managed by this provider (Swing
     *         {@code CachingSettingsProvider.getCachingSettings})
     */
    static ProofCachingSettings getCachingSettings() {
        return CACHING_SETTINGS;
    }

    @Override
    public int getPriorityOfSettings() {
        // extension: MP9.1 — sorted last like Swing (CachingSettingsProvider.java:118-121).
        return 10000;
    }
}
