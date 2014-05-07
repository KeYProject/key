/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.logic.PosInOccurrence;
import javax.swing.KeyStroke;


/**
 *
 * @author christoph
 */
public class DummyProofMacro implements ProofMacro {


    @Override
    public String getName() {
        return "DummyProofMacro";
    }


    @Override
    public String getDescription() {
        return "Does nothing";
    }


    @Override
    public boolean canApplyTo(KeYMediator mediator,
                              PosInOccurrence posInOcc) {
        return true;
    }


    @Override
    public void applyTo(KeYMediator mediator,
                        PosInOccurrence posInOcc,
                        ProverTaskListener listener) throws InterruptedException {
        // do nothing
    }


    @Override
    public KeyStroke getKeyStroke() {
        return null;  // default implementation
    }

}
