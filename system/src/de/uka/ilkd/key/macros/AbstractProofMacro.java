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
import de.uka.ilkd.key.gui.utilities.KeyStrokeManager;
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

    /**
     * The max number of steps to be applied.
     * A value of -1 means no changes.
     */
    private int numberSteps = -1;

    private static ImmutableList<Goal> getGoals(Node node) {
        if (node == null) {
            // can happen during initialisation
            return ImmutableSLList.<Goal>nil();
        } else {
            return node.proof().getSubtreeEnabledGoals(node);
        }
    }

    @Override
    public void setNumberSteps(int numberSteps) {
        this.numberSteps = numberSteps;
    }

    @Override
    public int getNumberSteps() {
        return this.numberSteps;
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


    @Override
    public final javax.swing.KeyStroke getKeyStroke() {
        return KeyStrokeManager.get(this);
    }
    
}