/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification.events;

import de.uka.ilkd.key.gui.fx.notification.NotificationEventIDF;

/**
 * A notification event caused by a general unexpected failure (usually caused by a bug of the
 * system).
 * <p>
 * Port of the Swing original {@code key.ui/src/main/java/de/uka/ilkd/key/gui/notification/
 * events/GeneralFailureEvent.java} (which is {@code @Deprecated} there in favor of
 * {@code IssueDialog}; the FX {@code IssueDialogF} is a future dialog-catalog item, until then
 * the framework keeps the same event shape).
 */
public class GeneralFailureEventF extends NotificationEventF {

    private String errorMessage = "Unknown Error.";

    protected GeneralFailureEventF(NotificationEventIDF id) {
        super(id);
    }

    /**
     * creates an instance of this event
     *
     * @param errorMessage a String describing the failure
     */
    public GeneralFailureEventF(String errorMessage) {
        super(NotificationEventIDF.GENERAL_FAILURE);
        this.errorMessage = errorMessage;
    }

    /**
     * @return the error message describing the reason for this event
     */
    public String getErrorMessage() {
        return errorMessage;
    }
}
