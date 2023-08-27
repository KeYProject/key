/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.notification.events;

import de.uka.ilkd.key.gui.notification.NotificationEventID;

public class ExceptionFailureEvent extends GeneralFailureEvent {

    private final Throwable error;

    public ExceptionFailureEvent(String string, Throwable throwable) {
        super(NotificationEventID.EXCEPTION_CAUSED_FAILURE);
        this.error = throwable;
    }

    public Throwable getException() {
        return error;
    }

}
