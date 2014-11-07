/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.ProverTaskListener;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;

/**
 * This macro does nothing and is not applicable. It can be used to create
 * compound macros, e.g. as an alternative macro for {@link DoWhileFinallyMacro}.
 *
 * @author christoph
 */
public class SkipMacro extends AbstractProofMacro {

    @Override
    public String getName() {
        return "SkipMacro";
    }


    @Override
    public String getDescription() {
        return "Does nothing";
    }

    @Override
    public boolean canApplyTo(KeYMediator mediator,
                              ImmutableList<Goal> goals,
                              PosInOccurrence posInOcc) {
        return false;
    }

    @Override
    public ProofMacroFinishedInfo applyTo(KeYMediator mediator,
                                          ImmutableList<Goal> goals,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws InterruptedException {
        // do nothing
        return new ProofMacroFinishedInfo(this, goals);
    }
}
