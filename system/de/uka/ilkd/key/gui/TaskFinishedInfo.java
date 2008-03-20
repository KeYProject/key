package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.proof.Proof;

/**
 * An information object with additional information about the 
 * finished task.
 */
public interface TaskFinishedInfo {
    Object getSource();

    Object getResult();

    long getTime();
    
    int getAppliedRules();

    int getClosedGoals();

    Proof getProof();
    
}
