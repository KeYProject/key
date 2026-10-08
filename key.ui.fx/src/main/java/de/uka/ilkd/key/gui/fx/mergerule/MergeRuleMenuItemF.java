/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.mergerule;

import javafx.application.Platform;
import javafx.scene.control.MenuItem;

import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF.Kind;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;

import org.key_project.prover.sequent.PosInOccurrence;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The menu item for the state merging rule ("State Merging Rule").
 * <p>
 * Port of the Swing {@code de.uka.ilkd.key.gui.mergerule.MergeRuleMenuItem} (key.ui): builds the
 * merge rule application for the given position, runs {@link MergeRuleCompletionF} (which shows
 * {@link MergePartnerSelectionDialogF}), and — if the completed application is applicable —
 * applies it interactively on a worker thread. Deviations: the Swing item used
 * {@code mediator.stopInterface/startInterface} and the {@code taskStarted/taskProgress/
 * taskFinished} plumbing of {@code mediator.getUI()}; the FX UI does not yet provide those
 * hooks (progress dialogs are a planned milestone), so errors are reported via the FX
 * notification layer ({@link NotificationManagerF}, Swing:
 * {@code mediator.notify(new ExceptionFailureEvent(...))}) and start/stop interface is left to
 * the caller.
 * <p>
 * Registration note: this item belongs into the future sequent-view context menu (Swing:
 * {@code CurrentGoalViewMenu.createMergeRuleMenu}); see the {@code joinmerge} TODO in
 * {@code MainWindowF}.
 *
 * @author Dominic Scheurer (original Swing menu item)
 * @see MergeRule
 */
public class MergeRuleMenuItemF extends MenuItem {

    private static final Logger LOGGER = LoggerFactory.getLogger(MergeRuleMenuItemF.class);

    /**
     * Creates a new menu item for the merge rule.
     *
     * @param goal The selected goal.
     * @param pio The position the merge shall be applied to (symbolic state / program counter
     *        formula).
     * @param proofControl the proof control used to apply the completed application
     *        interactively (Swing: {@code mediator.getUI().getProofControl()})
     */
    public MergeRuleMenuItemF(final Goal goal, final PosInOccurrence pio,
            final ProofControl proofControl) {
        final var services = goal.proof().getServices();

        setText(toString());

        setOnAction(e -> {
            final MergeRule mergeRule = MergeRule.INSTANCE;
            final MergeRuleBuiltInRuleApp app =
                (MergeRuleBuiltInRuleApp) mergeRule.createApp(pio, services);
            final MergeRuleCompletionF completion = MergeRuleCompletionF.INSTANCE;
            final MergeRuleBuiltInRuleApp completedApp =
                (MergeRuleBuiltInRuleApp) completion.complete(app, goal, false);

            // The completedApp may be null if the completion was not
            // possible (e.g., if no candidates were selected by the
            // user in the displayed dialog).
            if (completedApp != null && completedApp.complete()) {
                LOGGER.info("Merging {} nodes", completedApp.getMergePartners().size());
                completedApp.registerProgressListener(
                    progress -> LOGGER.debug("Merge progress: {}", progress));
                // Swing ran applyInteractive inside a SwingWorker; the FX analogue is a worker
                // thread with the result marshalled back via Platform.runLater
                Thread worker = new Thread(() -> {
                    try {
                        proofControl.applyInteractive(completedApp, goal);
                        Platform.runLater(() -> {
                            completedApp.clearProgressListeners();
                            LOGGER.info("Merging of {} nodes finished",
                                completedApp.getMergePartners().size());
                            NotificationManagerF.getInstance()
                                    .notify("Merging finished", Kind.INFO);
                        });
                    } catch (final Exception | AssertionError exc) {
                        signalError(exc);
                    }
                }, "fx-merge-rule-applier");
                worker.setDaemon(true);
                worker.start();
            }
        });
    }

    private void signalError(final Throwable e) {
        LOGGER.error("Merge rule application failed", e);
        Platform.runLater(() -> NotificationManagerF.getInstance()
                .notify("Merge rule application failed: " + e.getMessage(), Kind.ERROR));
    }

    @Override
    public String toString() {
        return "State Merging Rule";
    }
}
