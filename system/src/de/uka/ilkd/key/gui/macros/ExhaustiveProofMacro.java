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
import de.uka.ilkd.key.util.Pair;
import java.util.HashMap;
import java.util.Map;

public abstract class ExhaustiveProofMacro implements ProofMacro {

    /** Cache for those nodes which have already been checked whether
        a given macro can be applied on them or not. */
    private static Map<Pair<ProofMacro, Node>, PosInOccurrence> isApplicableOnNode =
            new HashMap<Pair<ProofMacro, Node>, PosInOccurrence>();

    private static PosInOccurrence getApplicablePosInOcc(KeYMediator mediator,
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
    public boolean canApplyTo(KeYMediator mediator, PosInOccurrence posInOcc) {
        final ProofMacro macro = getProofMacro();
        assert macro != null;
        assert mediator != null;
        assert mediator.getSelectionModel() != null;
        final Proof proof = mediator.getSelectedProof();
        if (proof == null) {
            // can happen during initialisation
            return false;
        }
        Goal savedSelectedGoal  = mediator.getSelectedGoal();
        for (final Goal goal : proof.openGoals()) {
            mediator.getSelectionModel().setSelectedGoal(goal);
            final Sequent seq = goal.sequent();
            final Pair<ProofMacro, Node> macroNodePair =
                    new Pair<ProofMacro, Node>(macro, goal.node());
            for (int i = 1; i <= seq.size(); i++) {
                if (!isApplicableOnNode.containsKey(macroNodePair)) {
                    final PosInOccurrence applicableAt =
                            getApplicablePosInOcc(
                                    mediator,
                                    PosInOccurrence.findInSequent(seq, i, PosInTerm.getTopLevel()),
                                    macro);
                    isApplicableOnNode.put(macroNodePair, applicableAt);
                }
                if (isApplicableOnNode.get(macroNodePair) != null) {
                    if (savedSelectedGoal != null) {
                        mediator.getSelectionModel().setSelectedGoal(savedSelectedGoal);
                    }
                    return true;
                }
            }
        }
        if (savedSelectedGoal != null) {
            mediator.getSelectionModel().setSelectedGoal(savedSelectedGoal);
        }
        return false;
    }

    @Override
    public void applyTo(KeYMediator mediator,
                        PosInOccurrence posInOcc,
                        ProverTaskListener listener) throws InterruptedException {
        final Proof proof = mediator.getSelectedProof();
        Goal savedSelectedGoal  = mediator.getSelectedGoal();
        for (Goal goal : proof.openGoals()) {
            mediator.getSelectionModel().setSelectedGoal(goal);
            final Sequent seq = goal.sequent();
            final ProofMacro macro = getProofMacro();
            final Pair<ProofMacro, Node> macroNodePair =
                    new Pair<ProofMacro, Node>(macro, goal.node());
            PosInOccurrence searchPos;
            for (int i = 1; i <= seq.size(); i++) {
                if (!isApplicableOnNode.containsKey(macroNodePair)) {
                    searchPos = PosInOccurrence.findInSequent(seq, i, PosInTerm.getTopLevel());
                    PosInOccurrence applicableAt =
                            getApplicablePosInOcc(mediator, searchPos, macro);
                    isApplicableOnNode.put(macroNodePair, applicableAt);
                }
                if (isApplicableOnNode.get(macroNodePair) != null) {
                    final PosInOccurrence pos = isApplicableOnNode.get(macroNodePair);
                    macro.applyTo(mediator, pos, listener);
                    if (savedSelectedGoal != null) {
                        mediator.getSelectionModel().setSelectedGoal(savedSelectedGoal);
                    }
                    return;
                }
            }
        }
        if (savedSelectedGoal != null) {
            mediator.getSelectionModel().setSelectedGoal(savedSelectedGoal);
        }
    }

    /**
     * Gets the proof macros.
     *
     * @return the proofMacro.
     */
    abstract ProofMacro getProofMacro();

    @Override
    public KeyStroke getKeyStroke() {
        return null; // default implementation
    }
}