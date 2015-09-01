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
package de.uka.ilkd.key.informationflow.macros;


import java.util.HashMap;
import java.util.Map;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.macros.AbstractProofMacro;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.macros.ProofMacroListener;
import de.uka.ilkd.key.proof.DefaultTaskStartedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.TaskStartedInfo.TaskKind;

/**
 * The abstract class ExhaustiveProofMacro can be used to create compound macros
 * which either apply the macro given by {@link getProofMacro()} directly, or
 * --if not directly applicable-- search on the sequent for any applicable
 * posInOcc and apply it on the first applicable one or --if not applicable
 * anywhere on the sequent-- do not apply it.
 *
 * @author Michael Kirsten
 */
public abstract class ExhaustiveProofMacro extends AbstractProofMacro {

    /** Cache for nodes which have already been checked for an applicable
        position. */
    private static Map<Node, PosInOccurrence> applicableOnNodeAtPos =
            new HashMap<Node, PosInOccurrence>();

    private PosInOccurrence getApplicablePosInOcc(Proof proof,
                                                  Goal goal,
                                                  PosInOccurrence posInOcc,
                                                  ProofMacro macro) {
        if (posInOcc == null || posInOcc.subTerm() == null) {
            return null;
        } else if (macro.canApplyTo(proof, ImmutableSLList.<Goal>nil().prepend(goal), posInOcc)) {
            return posInOcc;
        } else {
            final Term subTerm = posInOcc.subTerm();
            PosInOccurrence res = null;
            for (int i = 0; i < subTerm.arity() && res == null; i++) {
                res = getApplicablePosInOcc(proof, goal, posInOcc.down(i), macro);
            }
            return res;
        }
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.gui.macros.ProofMacro#getName()
     */
    @Override
    public String getName() {
        return "Apply macro on first applicable position in the sequent.";
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.gui.macros.ProofMacro#getDescription()
     */
    @Override
	public String getDescription() {
		return "Applies specificed macro --if it is applicable anywhere on" +
				"the sequent-- either directly or on the first applicable" +
				"position found.";
    }

    @Override
    public boolean canApplyTo(Proof proof,
                              ImmutableList<Goal> goals,
                              PosInOccurrence posInOcc) {
        Sequent seq = null;
        boolean applicable = false;
        final ProofMacro macro = getProofMacro();
        for (final Goal goal: goals) {
            seq = goal.sequent();
            if (!applicableOnNodeAtPos.containsKey(goal.node())) {
                // node has not been checked before, so do it
                for (int i = 1; i <= seq.size() &&
                                applicableOnNodeAtPos.get(goal.node()) == null; i++) {
                    PosInOccurrence searchPos =
                            PosInOccurrence.findInSequent(seq, i, PosInTerm.getTopLevel());
                    PosInOccurrence applicableAt =
                            getApplicablePosInOcc(proof, goal, searchPos, macro);
                    applicableOnNodeAtPos.put(goal.node(), applicableAt);
                }
            }
            applicable = applicable || applicableOnNodeAtPos.get(goal.node()) != null;
        }
        return applicable;
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic,
                                          Proof proof,
                                          ImmutableList<Goal> goals,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws InterruptedException, Exception {
        ProofMacroFinishedInfo info = new ProofMacroFinishedInfo(this, goals);
        final ProofMacro macro = getProofMacro();
        for (final Goal goal : goals) {
            if (!applicableOnNodeAtPos.containsKey(goal.node())) {
                // node has not been checked before, so do it
                boolean canBeApplied =
                        canApplyTo(proof, ImmutableSLList.<Goal>nil().prepend(goal), posInOcc);
                if (!canBeApplied) {
                    // canApplyTo checks all open goals. thus, if it returns
                    // false, then this macro is not applicable at all and
                    // we can return
                    return new ProofMacroFinishedInfo(this, goal);
                }
            }
            PosInOccurrence applicableAt = applicableOnNodeAtPos.get(goal.node());
            if (applicableAt != null) {
                final ProverTaskListener pml =
                        new ProofMacroListener(macro.getName(), listener);
                pml.taskStarted(new DefaultTaskStartedInfo(TaskKind.Macro, getName(), 0));
                synchronized(macro) {
                    // wait for macro to terminate
                    info = macro.applyTo(uic, proof, ImmutableSLList.<Goal>nil().prepend(goal),
                                         applicableAt, pml);
                }
                pml.taskFinished(info);
                info = new ProofMacroFinishedInfo(this, info);
            }
        }
        return info;
    }

    /**
     * Gets the proof macros.
     * <p/>
     * @return the proofMacro.
     */
    abstract ProofMacro getProofMacro();
}