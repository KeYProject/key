/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.notification.events;

import de.uka.ilkd.key.gui.notification.NotificationEventID;
import de.uka.ilkd.key.proof.Proof;


/**
 * NotificationEvent used to inform the user about a closed proof.
 *
 * @author bubel
 */
public class ProofClosedNotificationEvent extends NotificationEvent {

    /** the closed proof */
    private final Proof proof;

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
