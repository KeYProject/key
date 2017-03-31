// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.joinrule;

import java.awt.event.ActionEvent;

import javax.swing.AbstractAction;
import javax.swing.JMenuItem;
import javax.swing.SwingUtilities;
import javax.swing.SwingWorker;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.notification.events.ExceptionFailureEvent;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.DefaultTaskFinishedInfo;
import de.uka.ilkd.key.proof.DefaultTaskStartedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.TaskStartedInfo.TaskKind;
import de.uka.ilkd.key.rule.join.JoinRule;
import de.uka.ilkd.key.rule.join.JoinRuleBuiltInRuleApp;

/**
 * The menu item for the "defocusing" join rule.
 *
 * @author Dominic Scheurer
 * @see JoinRule
 */
public class JoinRuleMenuItem extends JMenuItem {
    private static final long serialVersionUID = -8509570987542243690L;

    /**
     * Creates a new menu item for the join rule.
     *
     * @param goal
     *            The selected goal.
     * @param pio
     *            The position the join shall be applied to (symbolic state /
     *            program counter formula).
     * @param mediator
     *            The KeY mediator.
     */
    public JoinRuleMenuItem(final Goal goal, final PosInOccurrence pio,
            final KeYMediator mediator) {
        final Services services = goal.proof().getServices();

        this.setText(toString());
        this.setAction(new AbstractAction(toString()) {
            private static final long serialVersionUID = 7695435228507302440L;

            @Override
            public void actionPerformed(ActionEvent e) {
                final JoinRule joinRule = JoinRule.INSTANCE;
                final JoinRuleBuiltInRuleApp app = (JoinRuleBuiltInRuleApp) joinRule
                        .createApp(pio, services);
                final JoinRuleCompletion completion = JoinRuleCompletion.INSTANCE;
                final JoinRuleBuiltInRuleApp completedApp = (JoinRuleBuiltInRuleApp) completion
                        .complete(app, goal, false);

                // The completedApp may be null if the completion was not
                // possible (e.g., if no candidates were selected by the
                // user in the displayed dialog).
                if (completedApp != null && completedApp.complete()) {
                    try {
                        mediator.stopInterface(true);

                        mediator.getUI()
                                .taskStarted(new DefaultTaskStartedInfo(
                                        TaskKind.Other,
                                        "Merging " + (completedApp
                                                .getJoinPartners().size() + 1)
                                                + " nodes",
                                        completedApp.getJoinPartners().size()));
                        mediator.getUI().taskProgress(0);

                        completedApp.registerProgressListener(progress -> {
                            mediator.getUI().setProgress(progress);
                        });

                        new SwingWorker<Void, Void>() {
                            private long duration;

                            @Override
                            protected Void doInBackground() throws Exception {
                                long time = System.currentTimeMillis();
                                goal.apply(completedApp);
                                duration = System.currentTimeMillis() - time;

                                return null;
                            }

                            @Override
                            protected void done() {
                                completedApp.clearProgressListeners();
                                mediator.getUI().taskFinished(
                                        new DefaultTaskFinishedInfo(this, goal,
                                                goal.proof(), duration, 1, 0));
                                mediator.startInterface(true);
                                mediator.getSelectionModel().setSelectedGoal(goal);
                            }
                        }.execute();
                    } catch (final Exception exc) {
                        signalError(exc, mediator);
                    } catch (final AssertionError exc) {
                        signalError(exc, mediator);
                    }
                }
            }
        });
    }

    private void signalError(final Throwable e, final KeYMediator mediator) {
        SwingUtilities.invokeLater(new Runnable() {
            @Override
            public void run() {
                mediator.notify(new ExceptionFailureEvent(e.getMessage(), e));
            }
        });
    }

    @Override
    public String toString() {
        return "(Defocusing) Join Rule";
    }
}
