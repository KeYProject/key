// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
// 
package de.uka.ilkd.key.gui;

import javax.swing.SwingWorker;

import de.uka.ilkd.key.core.InterruptListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.ProverTaskListener;
import de.uka.ilkd.key.core.TaskFinishedInfo;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.Debug;

/**
 * The Class ProofMacroWorker is a swing worker for the application of proof
 * macros.
 *
 * It decouples proof macros from the GUI event thread. It registers with the
 * mediator to receive Stop-Button events
 */
public class ProofMacroWorker extends SwingWorker<Void, Void> implements InterruptListener {

    /**
     * This flag decides whether after a macro an open is selected or not.
     * If the macro closed all goals under the current pio, selection remains
     * where it was.
     */
    private static final boolean SELECT_GOAL_AFTER_MACRO =
            Boolean.parseBoolean(System.getProperty("key.macro.selectGoalAfter", "true"));

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
     * Instantiates a new proof macro worker.
     *
     * @param macro the macro, not null
     * @param mediator the mediator, not null
     * @param posInOcc the position, possibly null
     */
    public ProofMacroWorker(ProofMacro macro, KeYMediator mediator, PosInOccurrence posInOcc) {
        assert macro != null;
        assert mediator != null;
        this.macro = macro;
        this.mediator = mediator;
        this.posInOcc = posInOcc;
    }

    @Override
    protected Void doInBackground() throws Exception {
        final ProverTaskListener ptl = mediator.getUI().getListener();
        TaskFinishedInfo info =
                ProofMacroFinishedInfo.getDefaultInfo(macro, mediator.getSelectedProof());
        ptl.taskStarted(macro.getName(), 0);
        try {
            synchronized(macro) {
                info = macro.applyTo(mediator, posInOcc, ptl);
            }
        } catch (final InterruptedException exception) {
            Debug.out("Proof macro has been interrupted:");
            Debug.out(exception);
        } catch (final Exception exception) {
            // This should actually never happen.
            ExceptionDialog.showDialog(MainWindow.getInstance(), exception);
        } finally {
            ptl.taskFinished(info);
        }
        return null;
    }

    @Override
    public void interruptionPerformed() {
        cancel(true);
    }

    @Override
    protected void done() {
        synchronized(macro) {
            if(SELECT_GOAL_AFTER_MACRO) {
                selectOpenGoalBelow();
            }
            mediator.setInteractive(true);
            mediator.startInterface(true);
            mediator.removeInterruptedListener(this);
        }
    }

    /*
     * Select a goal below the currently selected node.
     * Does not do anything if that is not available.
     * Only enabled goals are considered.
     */
    private void selectOpenGoalBelow() {
        Node selectedNode = mediator.getSelectedNode();
        for (Goal g : mediator.getInteractiveProver().getProof().openEnabledGoals()) {
            Node n = g.node();
            while(n != null) {
                if(n == selectedNode) {
                    mediator.getSelectionModel().setSelectedGoal(g);
                    return;
                }
                n = n.parent();
            }
        }
    }
}
