// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.gui.macros;

import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import java.util.HashMap;
import java.util.Map;


public abstract class ExhaustiveProofMacro implements ProofMacro {

    /** Cache for nodes which have already been checked for an applicable
     * position. */
    private Map<Node, PosInOccurrence> applicalbeOnNodeAtPos =
            new HashMap<Node, PosInOccurrence>();

    public boolean finishAfterMacro() {
        return true;
    }

    private PosInOccurrence getApplicablePosInOcc(KeYMediator mediator,
                                                  PosInOccurrence posInOcc,
                                                  ProofMacro macro) {
        if (posInOcc == null || posInOcc.subTerm() == null) {
            return null;
        } else if (macro.canApplyTo(mediator, posInOcc)) {
            return posInOcc;
        }
        Term subTerm = posInOcc.subTerm();
        PosInOccurrence res = null;
        for (int i = 0; i < subTerm.arity() && res == null; i++) {
            res = getApplicablePosInOcc(mediator, posInOcc.down(i), macro);
        }
        return res;
    }


    @Override
    public boolean canApplyTo(KeYMediator mediator,
                              PosInOccurrence posInOcc) {
        final ProofMacro macro = getProofMacro();

        assert macro != null;
        assert mediator != null;
        assert mediator.getSelectionModel() != null;

        if (mediator.getSelectedProof() == null) {
            // can happen during initialisation
            return false;
        }

        // stop interface, because the following changes of the goals should
        // not be observable in the interface
        // --> didn't work...
//        mediator.stopInterface(true);
//        mediator.setInteractive(false);

        // save the original selected goal and the original selected node
        Goal savedSelectedGoal = mediator.getSelectedGoal();
        Node savedSelectedNode = mediator.getSelectedNode();

        // check whether macro can be applied
        boolean isApplicable = canApplyToWorker(mediator, posInOcc, macro);

        // restart interface
//        mediator.startInterface(true);
//        mediator.setInteractive(true);

        // restore the original selected goal and the original selected node
        if (savedSelectedGoal != null) {
            mediator.getSelectionModel().setSelectedGoal(savedSelectedGoal);
        }
        if (savedSelectedNode != null) {
            mediator.getSelectionModel().setSelectedNode(savedSelectedNode);
        }

        return isApplicable;
    }


    public boolean canApplyToWorker(KeYMediator mediator,
                                    PosInOccurrence posInOcc,
                                    ProofMacro macro) {
        final Proof proof = mediator.getSelectedProof();
        for (Goal goal : proof.openGoals()) {
            mediator.getSelectionModel().setSelectedGoal(goal);
            final Sequent seq = goal.sequent();
            if (!applicalbeOnNodeAtPos.containsKey(goal.node())) {
                // node has not been checked before, so do it
                for (int i = 1; i <= seq.size() &&
                                applicalbeOnNodeAtPos.get(goal.node()) == null; i++) {
                    PosInOccurrence searchPos =
                            PosInOccurrence.findInSequent(seq, i, PosInTerm.getTopLevel());
                    PosInOccurrence applicableAt =
                            getApplicablePosInOcc(mediator, searchPos, macro);
                    applicalbeOnNodeAtPos.put(goal.node(), applicableAt);
                }
            }
            if (applicalbeOnNodeAtPos.get(goal.node()) != null) {
                // applicable position found
                return true;
            }
        }
        // no applicable postition found
        return false;
    }


    @Override
    public void applyTo(KeYMediator mediator,
                        PosInOccurrence posInOcc,
                        ProverTaskListener listener) throws InterruptedException {
        final Proof proof = mediator.getSelectedProof();

        // save the original selected goal and the original selected node
        Goal savedSelectedGoal = mediator.getSelectedGoal();
        Node savedSelectedNode = mediator.getSelectedNode();

        // apply macro
        applyToWorker(mediator, posInOcc, listener);

        // restore the original selected goal and the original selected node
        if (savedSelectedGoal != null) {
            mediator.getSelectionModel().setSelectedGoal(savedSelectedGoal);
        }
        if (savedSelectedNode != null) {
            mediator.getSelectionModel().setSelectedNode(savedSelectedNode);
        }
    }


    public void applyToWorker(KeYMediator mediator,
                              PosInOccurrence posInOcc,
                              ProverTaskListener listener) throws InterruptedException {
        final Proof proof = mediator.getSelectedProof();

        for (Goal goal : proof.openGoals()) {
            mediator.getSelectionModel().setSelectedGoal(goal);
            final Sequent seq = goal.sequent();
            final ProofMacro macro = getProofMacro();
            if (!applicalbeOnNodeAtPos.containsKey(goal.node())) {
                // node has not been checked before, so do it
                boolean canBeApplied = canApplyTo(mediator, posInOcc);
                if (!canBeApplied) {
                    // canApplyTo checks all open goals. thus, if it returns
                    // false, then this macro is not applicable at all and
                    // we can return
                    return;
                }
            }
            PosInOccurrence applicableAt =
                    applicalbeOnNodeAtPos.get(goal.node());
            if (applicableAt != null) {
                macro.applyTo(mediator, applicableAt, listener);
                return;
            }
        }
    }


    /**
     * Gets the proof macros.
     * <p/>
     * @return the proofMacro.
     */
    abstract ProofMacro getProofMacro();


    @Override
    public KeyStroke getKeyStroke() {
        return null; // default implementation
    }
}