package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.logic.PosInOccurrence;

/**
 * This abstract class ensures that method
 *  {@link #applyTo(KeYMediator, PosInOccurrence, ProverTaskListener)} 
 *  is synchronized and is basically a wrapper of method {@link #delegateApplyTo} 
 *  which has to be implemented by subclasses instead of {@link #applyTo(KeYMediator, PosInOccurrence, ProverTaskListener)}.
 * 
 */
public abstract class AbstractProofMacro implements ProofMacro {

    @Override
    public synchronized void applyTo(KeYMediator mediator, PosInOccurrence posInOcc,
            ProverTaskListener listener) throws InterruptedException {
        delegateApplyTo(mediator, posInOcc, listener);
    }
    
    protected abstract void delegateApplyTo(KeYMediator mediator, PosInOccurrence posInOcc,
            ProverTaskListener listener) throws InterruptedException;

}
