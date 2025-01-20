/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.mergerule;

import java.awt.event.ActionEvent;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.notification.events.ExceptionFailureEvent;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.prover.TaskStartedInfo.TaskKind;
import de.uka.ilkd.key.prover.impl.DefaultTaskFinishedInfo;
import de.uka.ilkd.key.prover.impl.DefaultTaskStartedInfo;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;

/**
 * The menu item for the state merging rule.
 *
 * @author Dominic Scheurer
 * @see MergeRule
 */
public class MergeRuleMenuItem extends JMenuItem {
    private static final long serialVersionUID = -8509570987542243690L;

    /**
     * Creates a new menu item for the join rule.
     *
     * @param goal The selected goal.
     * @param pio The position the join shall be applied to (symbolic state / program counter
     *        formula).
     * @param mediator The KeY mediator.
     */
    public MergeRuleMenuItem(final Goal goal, final PosInOccurrence pio,
            final KeYMediator mediator) {
        final Services services = goal.proof().getServices();

        this.setText(toString());
        this.setAction(new AbstractAction(toString()) {
            private static final long serialVersionUID = 7695435228507302440L;

            @Override
            public void actionPerformed(ActionEvent e) {
                final MergeRule joinRule = MergeRule.INSTANCE;
                final MergeRuleBuiltInRuleApp app =
                    (MergeRuleBuiltInRuleApp) joinRule.createApp(pio, services);
                final MergeRuleCompletion completion = MergeRuleCompletion.INSTANCE;
                final MergeRuleBuiltInRuleApp completedApp =
                    (MergeRuleBuiltInRuleApp) completion.complete(app, goal, false);

                // The completedApp may be null if the completion was not
                // possible (e.g., if no candidates were selected by the
                // user in the displayed dialog).
                if (completedApp != null && completedApp.complete()) {
                    try {
                        mediator.stopInterface(true);

                        mediator.getUI()
                                .taskStarted(new DefaultTaskStartedInfo(
                                    TaskKind.Other, "Merging "
                                        + (completedApp.getMergePartners().size() + 1) + " nodes",
                                    completedApp.getMergePartners().size()));
                        mediator.getUI().taskProgress(0);

                        completedApp.registerProgressListener(
                            progress -> mediator.getUI().setProgress(progress));

                        new SwingWorker<Void, Void>() {
                            private long duration;

                            @Override
                            protected Void doInBackground() throws Exception {
                                long time = System.currentTimeMillis();
                                mediator.getUI().getProofControl().applyInteractive(completedApp,
                                    goal);
                                duration = System.currentTimeMillis() - time;

                                return null;
                            }

                            @Override
                            protected void done() {
                                completedApp.clearProgressListeners();
                                mediator.getUI().taskFinished(
                                    new DefaultTaskFinishedInfo(MergeRuleMenuItem.this,
                                        goal, goal.proof(), duration, 1, 0));
                                mediator.startInterface(true);
                                mediator.getSelectionModel().setSelectedGoal(goal);
                            }
                        }.execute();
                    } catch (final Exception | AssertionError exc) {
                        signalError(exc, mediator);
                    }
                }
            }
        });
    }

    private void signalError(final Throwable e, final KeYMediator mediator) {
        SwingUtilities
                .invokeLater(() -> mediator.notify(new ExceptionFailureEvent(e.getMessage(), e)));
    }

    @Override
    public String toString() {
        return "State Merging Rule";
    }
}
