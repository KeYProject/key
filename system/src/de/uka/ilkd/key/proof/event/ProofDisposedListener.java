package de.uka.ilkd.key.proof.event;

import de.uka.ilkd.key.proof.Proof;

/**
 * Observes a {@link Proof}.
 * @author Martin Hentschel
 */
public interface ProofDisposedListener {
   /**
    * When a {@link Proof} was disposed via {@link Proof#dispose()}.
    * @param e The event.
    */
   public void proofDisposed(ProofDisposedEvent e);
}
