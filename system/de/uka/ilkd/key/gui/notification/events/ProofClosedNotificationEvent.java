/*
 * Created on 17.03.2005
 */
package de.uka.ilkd.key.gui.notification.events;

import de.uka.ilkd.key.gui.notification.NotificationEventID;
import de.uka.ilkd.key.proof.Proof;


/**
 * NotificationEvent used to inform the user about a closed proof.
 * @author bubel
 */
public class ProofClosedNotificationEvent extends NotificationEvent {

    /** the closed proof */
    private Proof proof;
    
    /** 
     * creates a proof closed notification event        
     */
    public ProofClosedNotificationEvent(Proof proof) {
        super(NotificationEventID.PROOF_CLOSED);   
        this.proof = proof;
    }

    /**
     * @return the proof that has been closed
     */
    public Proof getProof() {        
        return proof;
    }
    
    
    

}
