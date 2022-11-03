package de.uka.ilkd.key.control;

import de.uka.ilkd.key.proof.ProofEvent;


public interface AutoModeListener {

    /**
     * invoked if automatic execution has started
     */
    void autoModeStarted(ProofEvent e);

    /**
     * invoked if automatic execution has stopped
     */
    void autoModeStopped(ProofEvent e);

}
