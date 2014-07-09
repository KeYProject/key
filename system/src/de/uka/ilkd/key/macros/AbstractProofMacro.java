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

package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

/**
 * Takes care of providing the whole ProofMacro interface by only making it
 * necessary to implement to most general application methods for a given
 * list of goals and translating the less general versions (firstly for a
 * given node and secondly having neither any goals nor a node). Although
 * all these methods can be redefined by inheritance, this is usually not
 * necessary, unless you know <tt>exactly</tt> what you are doing.
 * The exception is {@link #finishAfterMacro()} for compound macros
 * (see description in {@link ProofMacro#finishAfterMacro()}).
 *
 * @author Michael Kirsten
 */
public abstract class AbstractProofMacro implements ProofMacro {

    private ImmutableList<Goal> goals = ImmutableSLList.<Goal>nil();
    private ProofMacroListener pml = null;

    private static ImmutableList<Goal> getGoals(Node node) {
        if (node == null) {
            // can happen during initialisation
            return ImmutableSLList.<Goal>nil();
        } else {
            return node.proof().getSubtreeEnabledGoals(node);
        }
    }

    private static boolean isGoalList(ImmutableList<?> list) {
        for (Object entry : list) {
            if (!(entry instanceof Goal)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public ImmutableList<Goal> getGoals() {
        return this.goals;
    }

    public final ProofMacroListener getListener() {
        return pml == null ? new ProofMacroListener(this) : pml;
    }

    @SuppressWarnings("unchecked")
    @Override
    public void innerMacroFinished(TaskFinishedInfo info) {
        if (info != null) {
            Object result = info.getResult();
            if (result instanceof ImmutableList<?> &&
                    isGoalList((ImmutableList<?>) result)) {
                this.goals = (ImmutableList<Goal>) result;
            }
        }
    }

    @Override
    public boolean finishAfterMacro() {
        return true;
    }

    @Override
    public boolean canApplyTo(KeYMediator mediator, PosInOccurrence posInOcc) {
        return canApplyTo(mediator, getGoals(mediator.getSelectedNode()), posInOcc);
    }

    @Override
    public boolean canApplyTo(KeYMediator mediator,
                              Node node,
                              PosInOccurrence posInOcc) {
        return canApplyTo(mediator, getGoals(node), posInOcc);
    }

    @Override
    public ProofMacroFinishedInfo applyTo(KeYMediator mediator,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws InterruptedException {
        return applyTo(mediator, getGoals(mediator.getSelectedNode()), posInOcc, listener);
    }

    @Override
    public ProofMacroFinishedInfo applyTo(KeYMediator mediator,
                                          Node node,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws InterruptedException {
        return applyTo(mediator, getGoals(node), posInOcc, listener);
    }
}