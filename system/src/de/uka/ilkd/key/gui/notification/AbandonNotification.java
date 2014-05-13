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

/*
 * Created on 18.03.2005
 */
package de.uka.ilkd.key.gui.notification;

import de.uka.ilkd.key.gui.notification.events.NotificationEvent;

/**
 * Notifies the user when a proof task is abandoned.
 * @author bubel
 */
public class AbandonNotification extends NotificationTask {

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.gui.notification.NotificationTask#executeImpl(de.uka.ilkd.key.gui.notification.NotificationEvent, de.uka.ilkd.key.gui.notification.NotificationManager)
     */
    protected void executeImpl(NotificationEvent event,
            NotificationManager manager) {
        for (final NotificationAction action : getNotificationActions()) {         
            action.execute(event);
        }
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.gui.notification.NotificationTask#getEventID()
     */
    public int getEventID() {
        return NotificationEventID.TASK_ABANDONED;
    }

}