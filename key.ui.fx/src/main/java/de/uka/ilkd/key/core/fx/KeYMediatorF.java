/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.core.fx;

import javafx.beans.property.ReadOnlyBooleanProperty;
import javafx.beans.property.ReadOnlyBooleanWrapper;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.proof.RuleAppListener;
import de.uka.ilkd.key.proof.io.AutoSaver;
import de.uka.ilkd.key.rule.OneStepSimplifier;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.javafx.FxUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The mediator of the JavaFX user interface, counter-part of {@code de.uka.ilkd.key.core.
 * KeYMediator} in the Swing module {@code key.ui}.
 * <p>
 * <b>Milestone M2, skeleton.</b> The mediator owns the {@link KeYSelectionModel} (it is the
 * model's {@link KeYSelectionModel.ProofBinder}: {@link #setProof(Proof, Proof)} is called
 * whenever the selected proof changes) and shares the {@link NotationInfo} of the displayed
 * proof: {@link #setProof(Proof, Proof)} swaps the proof listeners, rebinds the proof's
 * abbreviation map into the notation info and refreshes the one-step simplifier — exactly like
 * the Swing mediator. Interactive rule applications re-default the selection
 * ({@link #defaultSelection()}) so the attached views update; during auto mode the events are
 * suspended by the core ({@code Proof#suspendNonEssentialListeners}) and the views refresh from
 * the final state on {@code autoModeStopped}.
 * <p>
 * Deliberately deferred: notifications ({@code ProofClosedNotificationEvent} needs the Swing
 * notification events of key.ui — the FX notification arrives with M3), user
 * action listeners and the task/progress plumbing of the Swing mediator. The auto saver is
 * wired since MP7 ({@link #setAutoSave(int)} / {@link #getAutoSaver()}, mirroring the Swing
 * mediator).
 */
public final class KeYMediatorF implements KeYSelectionModel.ProofBinder {

    private static final Logger LOGGER = LoggerFactory.getLogger(KeYMediatorF.class);

    /** the notation info shared by all views printing terms/sequents (abbreviations, unicode). */
    private final NotationInfo notationInfo = new NotationInfo();

    /** the selection model, {@link #setProof(Proof, Proof)} is bound as its {@link ProofBinder}. */
    private final KeYSelectionModel keySelectionModel = new KeYSelectionModel(this);

    private final ProofTreeListener proofTreeListener = new MediatorProofTreeListener();

    private final RuleAppListenerProofListener proofListener = new RuleAppListenerProofListener();

    /** number of goals closed by the last auto mode run (for the status line in M3). */
    private int goalsClosedByAutoMode;

    /** whether an auto mode run is currently active (tracked via {@link #proofListener}). */
    private volatile boolean inAutoMode;

    /** the proof control this mediator is attached to, may be {@code null} until M3. */
    private ProofControl proofControl;

    /**
     * menu: MP7 — the optional {@link AutoSaver} (Swing {@code KeYMediator} field,
     * KeYMediator.java:85-87); armed/disarmed via {@link #setAutoSave(int)}, the saver follows
     * the selected proof through {@link #setProof(Proof, Proof)}.
     */
    private AutoSaver autoSaver;

    /**
     * Observable auto mode state for the UI (buttons and menu items bind their enabled state to
     * it); updated on the FX thread from the auto mode events.
     */
    private final ReadOnlyBooleanWrapper autoModeRunning =
        new ReadOnlyBooleanWrapper(this, "autoModeRunning");

    /**
     * Creates the mediator. The selection model is owned by the mediator; views and the main
     * window obtain it via {@link #getSelectionModel()}.
     */
    public KeYMediatorF() {
    }

    /**
     * Registers the mediator's auto mode listener on the given proof control (the Swing ctor does
     * this with {@code ui.getProofControl()}). Without attachment the mediator still works, but
     * {@link #isInAutoMode()} stays {@code false}.
     *
     * @param control the proof control of the application
     */
    public void attach(ProofControl control) {
        this.proofControl = control;
        control.addAutoModeListener(proofListener);
    }

    /**
     * {@inheritDoc}
     * <p>
     * Swaps the mediator's proof listeners to the new proof, rebinds the proof's abbreviation map
     * into the shared {@link #getNotationInfo() notation info} and refreshes the one-step
     * simplifier (Swing {@code KeYMediator#setProof}).
     */
    @Override
    public void setProof(Proof newProof, Proof previousProof) {
        if (previousProof == newProof) {
            return;
        }
        LOGGER.debug("Mediator binding proof: {} -> {}",
            previousProof == null ? null : previousProof.name(),
            newProof == null ? null : newProof.name());
        if (previousProof != null) {
            previousProof.removeProofTreeListener(proofTreeListener);
            previousProof.removeRuleAppListener(proofListener);
        }
        if (newProof != null) {
            notationInfo.setAbbrevMap(newProof.abbreviations());
            newProof.addProofTreeListener(proofTreeListener);
            newProof.addRuleAppListener(proofListener);
        }
        // menu: MP7 — the auto saver follows the selected proof (Swing
        // {@code KeYMediator.setProof}, KeYMediator.java:240-241: {@code
        // getAutoSaver().setProof(newProof)}); the saver accepts {@code null} (abandoned proof)
        if (getAutoSaver() != null) {
            getAutoSaver().setProof(newProof);
        }
        OneStepSimplifier.refreshOSS(newProof);
    }

    /**
     * menu: MP7 — arms or disarms the {@link AutoSaver} (Swing {@code KeYMediator.setAutoSave},
     * KeYMediator.java:148-150: {@code autoSaver = interval > 0 ? new AutoSaver(interval, true)
     * : null}); the saver writes intermediate .key artifacts every {@code interval} proof steps
     * and the final closed proof (see {@link AutoSaver}).
     *
     * @param interval the save interval in proof steps, 0 disables auto save
     */
    public void setAutoSave(int interval) {
        autoSaver = interval > 0 ? new AutoSaver(interval, true) : null;
    }

    /**
     * @return the auto saver to use, or {@code null} if auto save is disabled (Swing
     *         {@code KeYMediator.getAutoSaver}, KeYMediator.java:791-796)
     */
    public AutoSaver getAutoSaver() {
        return autoSaver;
    }

    /**
     * @return the selection model of the mediator
     */
    public KeYSelectionModel getSelectionModel() {
        return keySelectionModel;
    }

    /**
     * @return the notation info shared by the views (abbreviation map follows the selected proof)
     */
    public NotationInfo getNotationInfo() {
        return notationInfo;
    }

    /**
     * @return the currently selected proof or {@code null}
     */
    public Proof getSelectedProof() {
        return keySelectionModel.getSelectedProof();
    }

    /**
     * @return the currently selected node or {@code null}
     */
    public Node getSelectedNode() {
        return keySelectionModel.getSelectedNode();
    }

    /**
     * @return the currently selected goal or {@code null}
     */
    public Goal getSelectedGoal() {
        return keySelectionModel.getSelectedGoal();
    }

    /**
     * @return the services of the selected proof or {@code null}
     */
    public Services getServices() {
        Proof selectedProof = getSelectedProof();
        return selectedProof != null ? selectedProof.getServices() : null;
    }

    /**
     * Selects the default node/goal of the selected proof (first open goal or a leaf) and fires
     * {@code selectedNodeChanged}.
     */
    public void defaultSelection() {
        keySelectionModel.defaultSelection();
    }

    /**
     * @return {@code true} if an auto mode run is currently active
     */
    public boolean isInAutoMode() {
        return inAutoMode;
    }

    /**
     * @return the observable auto mode state (updated on the FX thread); the automatic proof
     *         buttons and menu items bind their disabled state to it
     */
    public ReadOnlyBooleanProperty autoModeRunningProperty() {
        return autoModeRunning.getReadOnlyProperty();
    }

    /**
     * Starts the automatic prover on the selected proof (Swing {@code AutoModeAction}: guarded by
     * {@code isInAutoMode} and {@code ProofControl#isAutoModeSupported}, then
     * {@code startAutoMode(proof, proof.openEnabledGoals())}). No-op without an attached proof
     * control, without a selected proof, while a run is active or when auto mode is not supported
     * for the proof.
     */
    public void startAutoMode() {
        Proof proof = getSelectedProof();
        if (proofControl == null || proof == null || inAutoMode
                || !proofControl.isAutoModeSupported(proof)) {
            return;
        }
        proofControl.startAutoMode(proof, proof.openEnabledGoals());
    }

    /** Stops the running automatic prover (Swing {@code AutoModeAction}); no-op when idle. */
    public void stopAutoMode() {
        if (proofControl != null && inAutoMode) {
            proofControl.stopAutoMode();
        }
    }

    /**
     * Undoes the last rule application on the selected goal (Swing {@code GoalBackAction}):
     * without a selected goal the newest goal of the selected node's subtree is used — the one
     * with the highest node serial number, where a closed goal wins if its serial is higher. As
     * in Swing, {@code Proof.pruneProof} refuses to prune a closed cutting point while
     * {@code GeneralSettings.noPruningClosed} is set (the default), so a goal back on a closed
     * branch is a no-op.
     */
    public void goalBack() {
        Node selNode = getSelectedNode();
        Goal selGoal = getSelectedGoal();
        if (selGoal == null && selNode != null) {
            selGoal = findNewestGoal(selNode);
        }
        if (selGoal != null) {
            setBack(selGoal);
            // set the selection to give the user a visual feedback (Swing GoalBackAction);
            // selGoal.node() is re-read after the prune, see setBack(Goal)
            keySelectionModel.setSelectedNode(selGoal.node());
        }
    }

    /**
     * Removes the proof subtree below the selected node (Swing {@code PruneProofAction}).
     */
    public void pruneProof() {
        Node node = getSelectedNode();
        if (node != null) {
            setBack(node);
        }
    }

    /**
     * Swing {@code KeYMediator.setBack(Goal)}: undoes the rule application that created the goal
     * ({@code ProofControl.pruneTo(Goal)} prunes to the goal's parent) and selects the pre-rule
     * node. The Swing task-finished notification is not yet mirrored.
     */
    private void setBack(Goal goal) {
        Proof proof = getSelectedProof();
        if (proof == null) {
            return;
        }
        if (goal.node().parent() != null) {
            // ProofControl.pruneTo(Goal): undo the rule application that created the goal's node
            proof.pruneProof(goal.node().parent());
        }
        // The goal's node must be re-read here: the pruner re-associates the goal with the
        // cutting point (Goal.pruneToParent), the old node is detached and its parent pointer
        // is cleared (Node.remove). Swing's KeYMediator.setBack reads goal.node() after
        // pruneTo as well.
        Node node = goal.node();
        keySelectionModel.setSelectedNode(node == proof.root() ? node : node.parent());
    }

    /**
     * Swing {@code KeYMediator.setBack(Node)}: prunes the subtree below the given node and
     * selects it.
     */
    private void setBack(Node node) {
        node.proof().pruneProof(node);
        keySelectionModel.setSelectedNode(node);
    }

    /**
     * Swing {@code GoalBackAction.findNewestGoal}: the goal of the subtree that was changed last
     * (the highest node serial number), open and closed goals considered.
     */
    private static Goal findNewestGoal(Node subtree) {
        if (subtree == null) {
            return null;
        }
        Proof proof = subtree.proof();
        ImmutableList<Goal> closedGoals = proof.getClosedSubtreeGoals(subtree);
        ImmutableList<Goal> openGoals = proof.getSubtreeGoals(subtree);
        int closedID = -1;
        Goal closed = null;
        int openID = -1;
        Goal open = null;
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

    /**
     * Counts a closed goal (called when a rule application produced no new goals).
     */
    public void closedAGoal() {
        goalsClosedByAutoMode++;
    }

    /**
     * @return the number of goals closed by the last auto mode run
     */
    public int getNrGoalsClosedByAutoMode() {
        return goalsClosedByAutoMode;
    }

    /**
     * Resets the closed-goal counter (called when an auto mode run starts).
     */
    public void resetNrGoalsClosedByHeuristics() {
        goalsClosedByAutoMode = 0;
    }

    /**
     * The mediator's proof tree listener (Swing {@code KeYMediatorProofTreeListener}): counts
     * closed goals, repairs the selection after pruning and logs proof closure (the notification
     * event follows in M3).
     */
    private final class MediatorProofTreeListener extends ProofTreeAdapter {
        @Override
        public void proofClosed(ProofTreeEvent e) {
            LOGGER.info("Proof closed: {}", e.getSource().name());
        }

        @Override
        public void proofPruned(ProofTreeEvent e) {
            FxUtil.runLater(() -> {
                Node selectedNode = keySelectionModel.getSelectedNode();
                if (selectedNode != null && !e.getSource().find(selectedNode)) {
                    keySelectionModel.setSelectedNode(e.getNode());
                }
            });
            OneStepSimplifier.refreshOSS(e.getSource());
        }

        @Override
        public void proofGoalsAdded(ProofTreeEvent e) {
            if (e.getGoals().isEmpty()) {
                // no new goals have been generated: the goal was closed
                closedAGoal();
            }
        }
    }

    /**
     * The mediator's rule application and auto mode listener (Swing {@code
     * KeYMediatorProofListener}): re-defaults the selection after interactive rule applications
     * so the views update, and tracks the auto mode state.
     */
    private final class RuleAppListenerProofListener implements RuleAppListener, AutoModeListener {

        @Override
        public void ruleApplied(ProofEvent e) {
            if (inAutoMode) {
                return;
            }
            if (e.getSource() == getSelectedProof()) {
                keySelectionModel.defaultSelection();
            }
        }

        @Override
        public void autoModeStarted(ProofEvent e) {
            inAutoMode = true;
            resetNrGoalsClosedByHeuristics();
            FxUtil.runLater(() -> autoModeRunning.set(true));
        }

        @Override
        public void autoModeStopped(ProofEvent e) {
            inAutoMode = false;
            FxUtil.runLater(() -> autoModeRunning.set(false));
        }
    }
}
