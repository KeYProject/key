/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification;

import de.uka.ilkd.key.gui.fx.notification.actions.ProofClosedDialogActionF;

/**
 * The proof closed notification notifies the user about a successful attempt closing a proof.
 * <p>
 * Port of the Swing original {@code key.ui/src/main/java/de/uka/ilkd/key/gui/notification/
 * ProofClosedNotification.java}. Runs also during auto mode (Swing
 * {@code automodeEnabledTask() == true}) since the automatic prover is usually what closes the
 * proof.
 */
public class ProofClosedNotificationF extends NotificationTaskF {

    /**
     * Creates a proof closed notification task with the FX proof-closed statistics dialog
     * (Swing parity: the constructor adding {@code ProofClosedJTextPaneDisplay}).
     */
    public ProofClosedNotificationF() {
        addNotificationAction(new ProofClosedDialogActionF());
    }

    @Override
    public NotificationEventIDF getEventID() {
        return NotificationEventIDF.PROOF_CLOSED;
    }

    /**
     * returns if this task should be executed in auto mode
     *
     * @return if true execute task even if in automode
     */
    @Override
    protected boolean automodeEnabledTask() {
        return true;
    }
}
