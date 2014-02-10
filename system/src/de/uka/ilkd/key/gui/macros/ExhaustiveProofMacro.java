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


    private PosInOccurrence getApplicablePosInOcc(KeYMediator mediator,
                                                  Goal goal,
                                                  PosInOccurrence posInOcc,
                                                  ExtendedProofMacro macro) {
        if (posInOcc == null || posInOcc.subTerm() == null) {
            return null;
        } else if (macro.canApplyTo(mediator, goal, posInOcc)) {
            return posInOcc;
        } else {
            Term subTerm = posInOcc.subTerm();
            for (int i = 0; i < subTerm.arity(); i++) {
                return getApplicablePosInOcc(mediator, goal, posInOcc.down(i), macro);
            }
            return null;
        }
    }


    @Override
    public boolean canApplyTo(KeYMediator mediator,
                              PosInOccurrence posInOcc) {
        final ExtendedProofMacro macro = getProofMacro();

        assert macro != null;
        assert mediator != null;
        assert mediator.getSelectionModel() != null;

        if (mediator.getSelectedProof() == null) {
            // can happen during initialisation
            return false;
        }

        // check whether macro can be applied
        final Proof proof = mediator.getSelectedProof();
        boolean isApplicable = false;
        for (Goal goal : proof.openGoals()) {
            isApplicable = isApplicable ||
                           canApplyTo(mediator, goal, posInOcc, macro);
        }

        return isApplicable;
    }


    public boolean canApplyTo(KeYMediator mediator,
                              Goal goal,
                              PosInOccurrence posInOcc,
                              ExtendedProofMacro macro) {
        final Sequent seq = goal.sequent();
        if (!applicalbeOnNodeAtPos.containsKey(goal.node())) {
            // node has not been checked before, so do it
            for (int i = 1; i <= seq.size() &&
                            applicalbeOnNodeAtPos.get(goal.node()) == null; i++) {
                PosInOccurrence searchPos =
                        PosInOccurrence.findInSequent(seq, i, PosInTerm.TOP_LEVEL);
                PosInOccurrence applicableAt =
                        getApplicablePosInOcc(mediator, goal, searchPos, macro);
                applicalbeOnNodeAtPos.put(goal.node(), applicableAt);
            }
        }
        return (applicalbeOnNodeAtPos.get(goal.node()) != null);
    }


    @Override
    public void applyTo(KeYMediator mediator,
                        PosInOccurrence posInOcc,
                        ProverTaskListener listener) throws InterruptedException {
        final Proof proof = mediator.getSelectedProof();

        for (Goal goal : proof.openGoals()) {
            final ExtendedProofMacro macro = getProofMacro();
            if (!applicalbeOnNodeAtPos.containsKey(goal.node())) {
                // node has not been checked before, so do it
                boolean canBeApplied = canApplyTo(mediator, goal,
                                                  posInOcc, macro);
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
                macro.applyTo(mediator, goal, applicableAt, listener);
            }
        }
    }


    /**
     * Gets the proof macros.
     * <p/>
     * @return the proofMacro.
     */
    abstract ExtendedProofMacro getProofMacro();


    @Override
    public KeyStroke getKeyStroke() {
        return null; // default implementation
    }
}