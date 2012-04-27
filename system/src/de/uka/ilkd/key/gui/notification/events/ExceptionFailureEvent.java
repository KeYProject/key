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
