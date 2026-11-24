/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification.events;

import de.uka.ilkd.key.gui.fx.notification.NotificationEventIDF;

/**
 * A failure notification event caused by an exception.
 * <p>
 * Port of the Swing original {@code key.ui/src/main/java/de/uka/ilkd/key/gui/notification/
 * events/ExceptionFailureEvent.java}.
 * <p>
 * termmenu/S4: fired by the load-failure path ({@code MainWindowF.setOnFailed}) and the
 * notification self-test; the default-registered {@code ExceptionFailureNotificationF}
 * surfaces the error toast.
 */
public class ExceptionFailureEventF extends GeneralFailureEventF {

    private final Throwable error;

    public ExceptionFailureEventF(String string, Throwable throwable) {
        super(NotificationEventIDF.EXCEPTION_CAUSED_FAILURE);
        this.error = throwable;
    }

    public Throwable getException() {
        return error;
    }
}
