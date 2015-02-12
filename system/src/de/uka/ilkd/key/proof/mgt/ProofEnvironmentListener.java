package de.uka.ilkd.key.proof.mgt;

import java.util.EventListener;

public interface ProofEnvironmentListener extends EventListener {

   public void proofRegistered(ProofEnvironmentEvent event);
   public void proofUnregistered(ProofEnvironmentEvent event);
   
   
}
