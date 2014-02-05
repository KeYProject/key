package de.uka.ilkd.key.proof.io.event;

import java.util.EventListener;

import de.uka.ilkd.key.proof.io.ProofSaver;

/**
 * Listens for changes on {@link ProofSaver} instances.
 * @author Martin Hentschel
 */
public interface ProofSaverListener extends EventListener {
   /**
    * This method is called when a file was saved via {@link ProofSaver#save()}.
    * @param e The {@link ProofSaverEvent}.
    */
   public void proofSaved(ProofSaverEvent e);
}
