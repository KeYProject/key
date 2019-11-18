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

package de.uka.ilkd.key.gui.notification;

import java.awt.Frame;

import de.uka.ilkd.key.gui.notification.actions.ExceptionFailureNotificationDialog;

public class ExceptionFailureNotification extends NotificationTask {
   
   public ExceptionFailureNotification(Frame parentComponent) {
      addNotificationAction(new ExceptionFailureNotificationDialog(parentComponent));
   }

    /**
     * returns if this task should be executed in auto mode
     * @return if true execute task even if in automode
     */
    @Override
   protected boolean automodeEnabledTask() {   
        return true;
    }

	@Override
	public NotificationEventID getEventID() {
		return NotificationEventID.EXCEPTION_CAUSED_FAILURE;
	}

}