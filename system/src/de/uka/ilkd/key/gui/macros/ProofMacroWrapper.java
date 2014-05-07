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
 * This class is a wrapper for normal proof macros to extended
 * proof macros.
 *
 * @author christoph
 */
public class ProofMacroWrapper implements ExtendedProofMacro {
    final ProofMacro wrappedMacro;

    /**
     * Constructs a ProofMacroWrapper with the passed macro.
     *
     * @param macro the macro to be wrapped.
     */
    public ProofMacroWrapper(ProofMacro macro) {
        this.wrappedMacro = macro;
    }

    /** {@inheritDoc} */
    @Override
    public String getName() {
        return wrappedMacro.getName();
    }


    /** {@inheritDoc} */
    @Override
    public String getDescription() {
        return wrappedMacro.getDescription();
    }

    public boolean finishAfterMacro() {
        return true;
    }

    /** {@inheritDoc} */
    @Override
    public boolean canApplyTo(KeYMediator mediator,
                              PosInOccurrence posInOcc) {
        return wrappedMacro.canApplyTo(mediator, posInOcc);
    }


    /** {@inheritDoc} */
    @Override
    public boolean canApplyTo(KeYMediator mediator,
                              Goal goal,
                              PosInOccurrence posInOcc) {
        return wrappedMacro.canApplyTo(mediator, posInOcc);
    }


    /** {@inheritDoc} */
    @Override
    public void applyTo(KeYMediator mediator,
                        PosInOccurrence posInOcc,
                        ProverTaskListener listener) throws InterruptedException {
        wrappedMacro.applyTo(mediator, posInOcc, listener);
    }


    /** {@inheritDoc} */
    @Override
    public void applyTo(KeYMediator mediator,
                        Goal goal,
                        PosInOccurrence posInOcc,
                        ProverTaskListener listener) throws InterruptedException {
        wrappedMacro.applyTo(mediator, posInOcc, listener);
    }


    /** {@inheritDoc} */
    @Override
    public KeyStroke getKeyStroke() {
        return wrappedMacro.getKeyStroke();
    }

}
