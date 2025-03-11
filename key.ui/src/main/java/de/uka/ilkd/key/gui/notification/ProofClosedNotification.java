/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.notification;

import javax.swing.JFrame;

import de.uka.ilkd.key.gui.notification.actions.ProofClosedJTextPaneDisplay;

/**
 * The proof closed notification notifies the user about a successful attempt closing a proof.
 *
 * @author bubel
 */
public class ProofClosedNotification extends NotificationTask {


    /**
     * Creates a proof closed notification task.
     */
    public ProofClosedNotification() {
    }

    public ProofClosedNotification(JFrame comp) {
        addNotificationAction(new ProofClosedJTextPaneDisplay(comp));
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

    /**
     * @return the event if of this task
     */
    @Override
    public NotificationEventID getEventID() {
        return NotificationEventID.PROOF_CLOSED;
    }
}
