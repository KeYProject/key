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
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

public abstract class AbstractProofMacro implements ProofMacro {

    private static ImmutableList<Goal> getGoals(KeYMediator mediator, Node node) {
        if (node == null) {
            // can happen during initialisation
            return ImmutableSLList.<Goal>nil();
        } else {
            return node.proof().getSubtreeEnabledGoals(node);
        }
    }

    @Override
    public boolean finishAfterMacro() {
        return true;
    }

    @Override
    public boolean canApplyTo(KeYMediator mediator, PosInOccurrence posInOcc) {
        return canApplyTo(mediator, getGoals(mediator, mediator.getSelectedNode()), posInOcc);
    }

    @Override
    public boolean canApplyTo(KeYMediator mediator,
                              Node node,
                              PosInOccurrence posInOcc) {
        return canApplyTo(mediator, getGoals(mediator, node), posInOcc);
    }

    @Override
    public void applyTo(KeYMediator mediator, PosInOccurrence posInOcc,
                        ProverTaskListener listener) throws InterruptedException {
        applyTo(mediator, getGoals(mediator, mediator.getSelectedNode()), posInOcc, listener);
    }

    @Override
    public void applyTo(KeYMediator mediator,
                        Node node,
                        PosInOccurrence posInOcc,
                        ProverTaskListener listener) throws InterruptedException {
        applyTo(mediator, getGoals(mediator, node), posInOcc, listener);
    }
}