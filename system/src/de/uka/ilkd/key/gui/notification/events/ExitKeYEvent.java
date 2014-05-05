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
package de.uka.ilkd.key.gui.notification.events;

import de.uka.ilkd.key.gui.notification.NotificationEventID;

/**
 * An exit key event indicating that KeY is currently shut down.
 * @author bubel
 */
public class ExitKeYEvent extends NotificationEvent {

    /**
     * creates an event fired when KeY is shutdown
     */
    public ExitKeYEvent() {
        super(NotificationEventID.EXIT_KEY);      
    }

}