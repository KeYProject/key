package org.key_project.key4eclipse.starter.core.util.event;

import java.util.EventListener;

import org.key_project.key4eclipse.starter.core.util.IProofProvider;

import de.uka.ilkd.key.proof.Proof;

/**
 * Observes changes on an {@link IProofProvider}.
 * @author Martin Hentschel
 */
public interface IProofProviderListener extends EventListener {
   /**
    * When the current {@link Proof} of {@link IProofProvider#getCurrentProof()} has changed.
    * @param e The event.
    */
   public void currentProofChanged(ProofProviderEvent e);
   
   /**
    * When the provided {@link Proof}s of {@link IProofProvider#getCurrentProofs()} have changed.
    * @param e The event.
    */
   public void currentProofsChanged(ProofProviderEvent e);
}
