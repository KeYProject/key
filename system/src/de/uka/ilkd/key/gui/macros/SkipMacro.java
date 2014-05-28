/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;

import javax.swing.KeyStroke;


/**
 *
 * @author christoph
 */
public class SkipMacro implements ProofMacro {

    @Override
    public String getName() {
        return "DummyProofMacro";
    }


    @Override
    public String getDescription() {
        return "Does nothing";
    }

    @Override
    public boolean finishAfterMacro() {
        return true;
    }

    @Override
    public boolean canApplyTo(KeYMediator mediator,
                              PosInOccurrence posInOcc) {
        return false;
    }

    @Override
    public boolean canApplyTo(KeYMediator mediator,
                              Goal goal,
                              PosInOccurrence posInOcc) {
        return canApplyTo(mediator, posInOcc);
    }

    @Override
    public void applyTo(KeYMediator mediator,
                        PosInOccurrence posInOcc,
                        ProverTaskListener listener) throws InterruptedException {
        // do nothing
    }

    @Override
    public void applyTo(KeYMediator mediator,
                        Goal goal,
                        PosInOccurrence posInOcc,
                        ProverTaskListener listener) throws InterruptedException {
        applyTo(mediator, posInOcc, listener);
    }

    @Override
    public KeyStroke getKeyStroke() {
        return null;  // default implementation
    }

}
