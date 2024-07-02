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
 * Created on 30.03.2005
 */
package de.uka.ilkd.key.gui.notification;

import javax.swing.JFrame;

import de.uka.ilkd.key.gui.notification.actions.GeneralInformationJTextPaneDisplay;

/**
 * This notification task is used to inform the user about a non-error
 * situation (e.g. statistics (how many goals have been closed) etc.) 
 * @author bubel
 */
public class GeneralInformationNotification extends NotificationTask {

    public GeneralInformationNotification(JFrame comp) {
       addNotificationAction(new GeneralInformationJTextPaneDisplay(comp));
   }

    /** 
     * @return the event id of a general information event
     * @see NotificationEventID
     */
    @Override
   public NotificationEventID getEventID() {
        return NotificationEventID.GENERAL_INFORMATION;
    }

}