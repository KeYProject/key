/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.settings;

import javafx.scene.control.Spinner;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

/**
 * The single/multi-core prover panel, FX port of {@code ParallelProverSettingsProvider} (Swing
 * {@code key.ui/settings/ParallelProverSettingsProvider.java}): toggles between the legacy
 * single-threaded prover and the multi-core (parallel) prover and configures the worker-thread
 * count of the latter (ParallelProverSettingsProvider.java:49-68). The multi-core prover trades
 * a set of single-core-only features (proof caching, slicing, the merge rule) for parallel proof
 * search; that trade-off is explained inline and enforced elsewhere by a listener on
 * {@link GeneralSettings#PARALLEL_PROVER_ENABLED}.
 */
final class ParallelProverSettingsProviderF extends SettingsPanelF implements SettingsProviderF {

    private static final String DESCRIPTION = "Prover (Single / Multi-Core)";

    private static final String INFO_ENABLED =
        "Run automatic proof search on several worker threads (one per open goal) instead of "
            + "the legacy single-threaded prover.\n\n"
            + "While the multi-core prover is active the single-core-only features are switched "
            + "off and restored when you switch back: proof caching, proof slicing, and the "
            + "merge rule (forced to 'skip' in the strategy options). Only the standard Java "
            + "profile runs in parallel; the well-definedness, information-flow and "
            + "symbolic-execution profiles always use the single-threaded prover.";

    private static final String INFO_THREADS =
        "Number of worker threads for the multi-core prover. The effective count is capped at "
            + "the number of available processors. Proofs that split widely benefit most; "
            + "narrow proofs are bounded by their longest branch.";

    private final javafx.scene.control.CheckBox chkEnabled;
    private final Spinner<Integer> spThreads;

    ParallelProverSettingsProviderF() {
        setHeaderText(DESCRIPTION);

        int availableProcessors = Runtime.getRuntime().availableProcessors();
        addSeparator("Multi-core prover");
        chkEnabled =
            addCheckBox("Use the multi-core prover (parallel proof search)", INFO_ENABLED, false);

        spThreads = addIntNumberField("Worker threads (max " + availableProcessors + ")", 1,
            Math.max(1, availableProcessors), 1, GeneralSettings.PARALLEL_PROVER_THREADS_DEFAULT,
            INFO_THREADS, null);
        // the worker count is a small number; the spinner enablement follows the checkbox like
        // the Swing updateEnabledState (ParallelProverSettingsProvider.java:70-72)
        spThreads.disableProperty().bind(chkEnabled.selectedProperty().not());
    }

    @Override
    public String getDescription() {
        return DESCRIPTION;
    }

    @Override
    public javafx.scene.Node getPanel(MainWindowF window) {
        GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
        chkEnabled.setSelected(gs.isParallelProverEnabled());
        int configured = Math.max(1, Math.min(gs.getParallelProverThreadCount(),
            Math.max(1, Runtime.getRuntime().availableProcessors())));
        spThreads.getValueFactory().setValue(configured);
        return this;
    }

    @Override
    public void apply(MainWindowF window) {
        GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
        gs.setParallelProverThreadCount(spThreads.getValue());
        // set the enabled flag last so the feature-gating listener sees the final thread count
        // (Swing ParallelProverSettingsProvider.java:90-96)
        gs.setParallelProverEnabled(chkEnabled.isSelected());
    }
}
