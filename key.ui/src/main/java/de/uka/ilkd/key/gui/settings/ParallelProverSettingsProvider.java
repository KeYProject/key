/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.settings;

import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

/**
 * Settings pane to choose between the legacy single-threaded prover and the multi-core (parallel)
 * prover, and to configure the worker-thread count of the latter.
 *
 * <p>
 * The multi-core prover trades a set of single-core-only features (proof caching, slicing, the
 * merge rule) for parallel proof search; that trade-off is explained inline and enforced
 * elsewhere by a listener on {@link GeneralSettings#PARALLEL_PROVER_ENABLED}.
 *
 */
public class ParallelProverSettingsProvider extends SettingsPanel implements SettingsProvider {

    private static final String DESCRIPTION = "Prover (Single / Multi-Core)";

    private static final String INFO_ENABLED =
        """
                Run automatic proof search on several worker threads (one per open goal) instead of the \
                legacy single-threaded prover.

                While the multi-core prover is active the single-core-only features are switched off and \
                restored when you switch back: proof caching, proof slicing, and the merge rule \
                (forced to 'skip' in the strategy options). Only the standard Java profile runs in \
                parallel; the well-definedness, information-flow and symbolic-execution profiles always \
                use the single-threaded prover.""";

    private static final String INFO_THREADS =
        """
                Number of worker threads for the multi-core prover. The effective count is capped at the \
                number of available processors. Proofs that split widely benefit most; narrow proofs are \
                bounded by their longest branch.""";

    private final int availableProcessors = Runtime.getRuntime().availableProcessors();

    private final JCheckBox chkEnabled;
    private final JSpinner spThreads;

    public ParallelProverSettingsProvider() {
        setHeaderText(getDescription());

        addSeparator("Multi-core prover");
        chkEnabled = addCheckBox("Use the multi-core prover (parallel proof search)", INFO_ENABLED,
            false, emptyValidator());

        spThreads = createNumberTextField(
            new SpinnerNumberModel(GeneralSettings.PARALLEL_PROVER_THREADS_DEFAULT, 1,
                Math.max(1, availableProcessors), 1),
            emptyValidator());
        // The worker count is a small number; keep the field narrow (room for three digits).
        if (spThreads.getEditor() instanceof JSpinner.DefaultEditor editor) {
            editor.getTextField().setColumns(3);
        }
        addTitledComponent("Worker threads (max " + availableProcessors + ")", spThreads,
            INFO_THREADS);

        chkEnabled.addActionListener(e -> updateEnabledState());
    }

    private void updateEnabledState() {
        spThreads.setEnabled(chkEnabled.isSelected());
    }

    @Override
    public String getDescription() {
        return DESCRIPTION;
    }

    @Override
    public JPanel getPanel(MainWindow window) {
        GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
        chkEnabled.setSelected(gs.isParallelProverEnabled());
        int configured = Math.max(1, Math.min(gs.getParallelProverThreadCount(),
            Math.max(1, availableProcessors)));
        spThreads.setValue(configured);
        updateEnabledState();
        return this;
    }

    @Override
    public void applySettings(MainWindow window) {
        GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
        gs.setParallelProverThreadCount((Integer) spThreads.getValue());
        // Set the enabled flag last so the feature-gating listener sees the final thread count.
        gs.setParallelProverEnabled(chkEnabled.isSelected());
    }
}
