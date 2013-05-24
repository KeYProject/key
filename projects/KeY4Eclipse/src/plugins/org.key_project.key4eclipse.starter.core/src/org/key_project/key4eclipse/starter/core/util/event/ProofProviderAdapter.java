package org.key_project.key4eclipse.starter.core.util.event;

/**
 * Adapter of {@link IProofProviderListener} which does nothing.
 * @author Martin Hentschel
 */
public class ProofProviderAdapter implements IProofProviderListener {
   /**
    * {@inheritDoc}
    */
   @Override
   public void currentProofChanged(ProofProviderEvent e) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void currentProofsChanged(ProofProviderEvent e) {
   }
}
