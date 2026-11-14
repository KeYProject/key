/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.notification.events;

import de.uka.ilkd.key.gui.notification.NotificationEventID;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public class ExceptionFailureEvent extends GeneralFailureEvent {

    private final Throwable error;

    /**
     * Creates an event for an exception that caused a failure.
     *
     * @param message the exception message, possibly {@code null} if the exception has none
     * @param throwable the exception that caused the failure
     */
    public ExceptionFailureEvent(@Nullable String message, Throwable throwable) {
        super(NotificationEventID.EXCEPTION_CAUSED_FAILURE);
        this.error = throwable;
    }

    public Throwable getException() {
        return error;
    }

}
