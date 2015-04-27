// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

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