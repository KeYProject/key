/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.util.ArrayList;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.control.InteractionListener;
import de.uka.ilkd.key.core.InterruptListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import de.uka.ilkd.key.prover.impl.DefaultTaskStartedInfo;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The Class ProofMacroWorker is a swing worker for the application of proof macros.
 * <p>
 * It decouples proof macros from the GUI event thread. It registers with the mediator to receive
 * Stop-Button events
 */
public class ProofMacroWorker extends SwingWorker<ProofMacroFinishedInfo, Void>
        implements InterruptListener {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofMacroWorker.class);

    /**
     * This flag decides whether after a macro an open is selected or not. If the macro closed all
     * goals under the current pio, selection remains where it was.
     */
    private static final boolean SELECT_GOAL_AFTER_MACRO =
        Boolean.parseBoolean(System.getProperty("key.macro.selectGoalAfter", "true"));

    /**
     * The {@link Node} to start macro at.
     */
    private final Node node;

    /**
     * The macro which is to be executed
     */
    private final ProofMacro macro;
    /**
     * The mediator of the environment
     */
    private final KeYMediator mediator;
    /**
     * This position may be null if no subterm selected
     */
    private final PosInOccurrence posInOcc;
    /**
     * The resulting information of the task or null if the task was cancelled an exception was
     * thrown
     */
    private ProofMacroFinishedInfo info;
    /**
     * The thrown exception leading to cancellation of the task
     */
    private Exception exception;
    private final List<InteractionListener> interactionListeners = new ArrayList<>();

    /**
     * Instantiates a new proof macro worker.
     *
     * @param node the {@link Node} to start macro at.
     * @param macro the macro, not null
     * @param mediator the mediator, not null
     * @param posInOcc the position, possibly null
     */
    public ProofMacroWorker(Node node, ProofMacro macro, KeYMediator mediator,
            PosInOccurrence posInOcc) {
        assert macro != null;
        assert mediator != null;
        this.node = node;
        this.macro = macro;
        this.mediator = mediator;
        this.posInOcc = posInOcc;
    }

    @Override
    protected ProofMacroFinishedInfo doInBackground() {
        final ProverTaskListener ptl = mediator.getUI();
        Proof selectedProof = node.proof();
        info = ProofMacroFinishedInfo.getDefaultInfo(macro, selectedProof);
        ptl.taskStarted(
            new DefaultTaskStartedInfo(TaskStartedInfo.TaskKind.Macro, macro.getName(), 0));
        try {
            synchronized (macro) {
                info = macro.applyTo(mediator.getUI(), node, posInOcc, ptl);
            }
        } catch (final InterruptedException exception) {
            LOGGER.debug("Proof macro has been interrupted:", exception);
            info = new ProofMacroFinishedInfo(macro, selectedProof, true);
            this.exception = exception;
        } catch (final Exception exception) {
            // This should actually never happen.
            this.exception = exception;
        }

        return info;
    }

    @Override
    public void interruptionPerformed() {
        cancel(true);
    }

    @Override
    protected void done() {
        synchronized (macro) {
            mediator.removeInterruptedListener(this);
            if (!isCancelled() && exception != null) { // user cancelled task is fine, we do not
                                                       // report this
                // This should actually never happen.
                LOGGER.error("", exception);
                IssueDialog.showExceptionDialog(MainWindow.getInstance(), exception);
            }

            mediator.getUI().taskFinished(info);

            if (SELECT_GOAL_AFTER_MACRO) {
                selectOpenGoalBelow();
            }

            mediator.setInteractive(true);
            mediator.startInterface(true);

            emitProofMacroFinished(node, macro, posInOcc, info);
        }
    }

    protected void emitProofMacroFinished(Node node, ProofMacro macro, PosInOccurrence posInOcc,
            ProofMacroFinishedInfo info) {
        interactionListeners.forEach((l) -> l.runMacro(node, macro, posInOcc, info));
    }

    public void addInteractionListener(InteractionListener listener) {
        interactionListeners.add(listener);
    }

    public void removeInteractionListener(InteractionListener listener) {
        interactionListeners.remove(listener);
    }

    /**
     * Select a goal below the currently selected node. Does not do anything if that is not
     * available. Only enabled goals are considered.
     */
    private void selectOpenGoalBelow() {
        Node selectedNode = mediator.getSelectedNode();
        for (Goal g : selectedNode.proof().openEnabledGoals()) {
            Node n = g.node();
            while (n != null) {
                if (n == selectedNode) {
                    mediator.getSelectionModel().setSelectedGoal(g);
                    return;
                }
                n = n.parent();
            }
        }
    }
}
