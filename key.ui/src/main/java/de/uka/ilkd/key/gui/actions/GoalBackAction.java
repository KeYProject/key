/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.GeneralSettings;

import org.key_project.util.collection.ImmutableList;

/**
 * This action is one part of the previous UndoLastStepAction: It undoes the last rule application
 * on the currently selected branch. It now also works on closed branches if the flag
 * "--no-pruning-closed" is not set (to save memory).
 *
 * The action is enabled if: 1. the proof is not empty (just the root node exists) and 2. either
 * pruning of closed branches is enabled or the selected node is open
 *
 * @author Pfeifer (enabled goalBack in closed branches)
 */
public final class GoalBackAction extends MainWindowAction {

    /**
     *
     */
    private static final long serialVersionUID = 4574670781882014062L;

    /**
     * indicates if long names (including the name of the rule to undo) are displayed
     */
    private boolean longName = false;

    /**
     * Creates a new GoalBackAction.
     *
     * @param mainWindow the main window this action belongs to
     * @param longName true iff long names (including the name of the rule to undo) shall be
     *        displayed (e.g. in menu items)
     */
    public GoalBackAction(MainWindow mainWindow, boolean longName) {
        super(mainWindow);
        this.longName = longName;
        putValue(SMALL_ICON, IconFactory.goalBackLogo(MainWindow.TOOLBAR_ICON_SIZE));
        putValue(SHORT_DESCRIPTION, "Undo the last rule application.");
        initListeners();
        updateName();
    }

    /**
     * Registers the action at some listeners to update its status in a correct fashion. This method
     * has to be invoked after the Main class has been initialized with the KeYMediator.
     */
    public void initListeners() {
        final KeYSelectionListener selListener = new KeYSelectionListener() {

            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                final Proof proof = getMediator().getSelectedProof();
                if (proof == null) {
                    // no proof loaded
                    setEnabled(false);
                } else {
                    final Node selNode = getMediator().getSelectedNode();
                    // enable/disable the action (see JavaDoc of class)
                    setEnabled(selNode != null && !proof.root().leaf()
                            && !(GeneralSettings.noPruningClosed && selNode.isClosed()));
                }
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                selectedNodeChanged(e);
            }
        };

        getMediator().addKeYSelectionListener(selListener);

        /*
         * This method delegates the request only to the UserInterfaceControl which implements the
         * functionality. No functionality is allowed in this method body!
         */
        getMediator().getUI().getProofControl().addAutoModeListener(new AutoModeListener() {
            @Override
            public void autoModeStarted(ProofEvent e) {
                getMediator().removeKeYSelectionListener(selListener);
                setEnabled(false);
            }

            @Override
            public void autoModeStopped(ProofEvent e) {
                getMediator().addKeYSelectionListener(selListener);
                selListener.selectedNodeChanged(null);
            }
        });
        selListener.selectedNodeChanged(new KeYSelectionEvent(getMediator().getSelectionModel()));
    }

    /**
     * Adds the displayName of the rule, which is affected by the undo operation, to the action.
     */
    public void updateName() {
        String appliedRule = "";
        if (longName && getMediator() != null) {
            final Goal goal = findNewestGoal(getMediator().getSelectedNode());
            if (goal != null && goal.node() != null && goal.node().parent() != null) {
                RuleApp app = goal.node().parent().getAppliedRuleApp();
                if (app != null) {
                    appliedRule = " (" + app.rule().displayName() + ")";
                }
            }
        }
        putValue(NAME, "Undo Last Rule Application" + appliedRule);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        final Node selNode = getMediator().getSelectedNode();

        /*
         * first check if a goal is selected, if not try to find one in the subtree under the
         * selected node
         */
        Goal selGoal = getMediator().getSelectedGoal();
        if (selGoal == null && selNode != null) {
            selGoal = findNewestGoal(selNode);
        }

        if (selGoal != null) {
            getMediator().setBack(selGoal);

            // set the selection to give the user a visual feedback
            getMediator().getSelectionModel().setSelectedNode(selGoal.node());
        }
    }

    /**
     * Finds the newest goal (the goal with the highest serial number) in the given subtree.
     *
     * @param subtree the root of the subtree to search. If it is null, the return value is null.
     * @return the newest goal in the given subtree or null, if no suitable goal is found in the
     *         open/closedGoals lists. This may be the case if the flag "--no-pruning-closed" is set
     *         (which means that the closedGoals list is empty) and the given subtree is closed.
     */
    private Goal findNewestGoal(Node subtree) {
        if (subtree == null) {
            return null;
        }

        final Proof proof = subtree.proof();

        ImmutableList<Goal> closedGoals = proof.getClosedSubtreeGoals(subtree);
        ImmutableList<Goal> openGoals = proof.getSubtreeGoals(subtree);

        /*
         * determine the goal which was last changed (which has the highest serial nr.) in this
         * branch
         */
        int closedID = -1;
        Goal closed = null;
        int openID = -1;
        Goal open = null;

        // if "--no-pruning-closed" is set, closedGoals is empty and this has no effect
        for (Goal g : closedGoals) {
            if (g.node().serialNr() > closedID) {
                closedID = g.node().serialNr();
                closed = g;
            }
        }

        for (Goal g : openGoals) {
            if (g.node().serialNr() > openID) {
                openID = g.node().serialNr();
                open = g;
            }
        }

        return closedID > openID ? closed : open;
    }
}
