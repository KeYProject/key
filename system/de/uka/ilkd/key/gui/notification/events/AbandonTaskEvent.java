// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
/*
 * Created on 18.03.2005
 */
package de.uka.ilkd.key.gui.notification.events;

import de.uka.ilkd.key.gui.notification.NotificationEventID;

/**
 * Emitted after removing a proof task
 * @author bubel
 */
public class AbandonTaskEvent extends NotificationEvent {

    /**
     * creates an event
     */
    public AbandonTaskEvent() {
        super(NotificationEventID.TASK_ABANDONED);        
    }

}
