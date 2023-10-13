/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.notification.events;

import de.uka.ilkd.key.gui.notification.NotificationEventID;

/**
 * A notification event caused by a general unexpected failure (usually caused by a bug of the
 * system)
 *
 * @deprecated use {@link de.uka.ilkd.key.gui.IssueDialog}
 * @author bubel
 */
@Deprecated
public class GeneralFailureEvent extends NotificationEvent {

    private String errorMessage = "Unknown Error.";


    protected GeneralFailureEvent(NotificationEventID id) {
        super(id);
    }

    /**
     * creates an instance of this event
     *
     * @param errorMessage a String describing the failure
     */
    public GeneralFailureEvent(String errorMessage) {
        super(NotificationEventID.GENERAL_FAILURE);
        this.errorMessage = errorMessage;
    }


    /**
     * @return the error message describing the reason for this event
     */
    public String getErrorMessage() {
        return errorMessage;
    }

}
