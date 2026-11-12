/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification.events;

import de.uka.ilkd.key.gui.fx.notification.NotificationEventIDF;
import de.uka.ilkd.key.proof.Proof;

/**
 * NotificationEvent used to inform the user about a closed proof.
 * <p>
 * Port of the Swing original {@code key.ui/src/main/java/de/uka/ilkd/key/gui/notification/
 * events/ProofClosedNotificationEvent.java}.
 */
public class ProofClosedNotificationEventF extends NotificationEventF {

    /** the closed proof */
    private final Proof proof;

    /**
     * creates a proof closed notification event
     */
    public ProofClosedNotificationEventF(Proof proof) {
        super(NotificationEventIDF.PROOF_CLOSED);
        this.proof = proof;
    }

    /**
     * @return the proof that has been closed
     */
    public Proof getProof() {
        return proof;
    }
}
