package de.uka.ilkd.key.proof.mgt;

import java.util.EventListener;

public interface ProofEnvironmentListener extends EventListener {

    void proofRegistered(ProofEnvironmentEvent event);

    void proofUnregistered(ProofEnvironmentEvent event);


}
