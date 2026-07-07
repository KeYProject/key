/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.settings;

import java.util.ArrayList;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import net.miginfocom.layout.CC;

/**
 * Settings pane to choose between the legacy single-threaded prover and the multi-core (parallel)
 * prover, and to configure the worker-thread count of the latter.
 *
 * <p>
 * The multi-core prover trades a set of single-core-only features (proof caching, slicing, the
 * merge
 * rule) for parallel proof search; that trade-off is explained inline and enforced elsewhere by a
 * listener on {@link GeneralSettings#PARALLEL_PROVER_ENABLED}.
 *
 * <p>
 * An "Advanced" button reveals expert prover internals: currently the eagerly maintained
 * rule-application queue ({@link GeneralSettings#isEagerRuleQueueEnabled()}). Both toggles are
 * machine-wide general settings -- prover infrastructure orthogonal to the proof strategy.
 *
 * @author Claude (KeY multithreading effort)
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

    private static final String INFO_EAGER_QUEUE =
        """
                Maintain each goal's rule-application queue eagerly (identity-anchored candidate \
                set updated by sequent-change events) instead of lazily revalidating candidates \
                when they surface. Produces the same proofs; substantially faster and leaner on \
                large sequents (wide arithmetic/heap proofs). Experimental: the classic queue \
                remains the default. Applies to proofs loaded or started after the change.""";

    private final int availableProcessors = Runtime.getRuntime().availableProcessors();

    private final JCheckBox chkEnabled;
    private final JSpinner spThreads;
    private final JButton btnAdvanced;
    private final JCheckBox chkEagerQueue;
    /** Components of the advanced section, hidden until the Advanced button is pressed. */
    private final List<JComponent> advancedComponents = new ArrayList<>();

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

        // ------- advanced section (hidden behind the button; hideMode 3 = ignore in layout)
        btnAdvanced = new JButton("Advanced…");
        btnAdvanced.setToolTipText("Show expert prover internals.");
        pCenter.add(new JLabel(), new CC().hideMode(3));
        pCenter.add(btnAdvanced, new CC().hideMode(3).wrap());

        final JLabel lblAdvanced = new JLabel("Advanced");
        final JSeparator sep = new JSeparator(SwingConstants.HORIZONTAL);
        pCenter.add(lblAdvanced, new CC().hideMode(3).spanX(1));
        pCenter.add(sep, new CC().hideMode(3).growX().spanX(2).wrap());

        chkEagerQueue = createCheckBox(
            "Use the eagerly maintained rule-application queue (experimental)", false,
            emptyValidator());
        final JLabel filler = new JLabel();
        final JLabel help = createHelpLabel(INFO_EAGER_QUEUE);
        pCenter.add(filler, new CC().hideMode(3));
        pCenter.add(chkEagerQueue, new CC().hideMode(3));
        pCenter.add(help, new CC().hideMode(3).wrap());

        advancedComponents.add(lblAdvanced);
        advancedComponents.add(sep);
        advancedComponents.add(filler);
        advancedComponents.add(chkEagerQueue);
        advancedComponents.add(help);
        setAdvancedVisible(false);

        btnAdvanced.addActionListener(e -> {
            btnAdvanced.setVisible(false);
            setAdvancedVisible(true);
            revalidate();
            repaint();
        });
    }

    private void setAdvancedVisible(boolean visible) {
        for (JComponent c : advancedComponents) {
            c.setVisible(visible);
        }
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
        final boolean eager = gs.isEagerRuleQueueEnabled();
        chkEagerQueue.setSelected(eager);
        // an active expert setting must be visible without pressing the button
        if (eager) {
            btnAdvanced.setVisible(false);
            setAdvancedVisible(true);
        }
        return this;
    }

    @Override
    public void applySettings(MainWindow window) {
        GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
        gs.setParallelProverThreadCount((Integer) spThreads.getValue());
        // Set the enabled flag last so the feature-gating listener sees the final thread count.
        gs.setParallelProverEnabled(chkEnabled.isSelected());

        final boolean before = gs.isEagerRuleQueueEnabled();
        gs.setEagerRuleQueueEnabled(chkEagerQueue.isSelected());
        if (before != gs.isEagerRuleQueueEnabled()) {
            JOptionPane.showMessageDialog(this,
                "The rule-application queue changes for proofs loaded or started from now on.");
        }
    }
}
