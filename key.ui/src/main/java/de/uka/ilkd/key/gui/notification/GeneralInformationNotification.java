/*
 * Created on 30.03.2005
 */
package de.uka.ilkd.key.gui.notification;

import javax.swing.JFrame;

import de.uka.ilkd.key.gui.notification.actions.GeneralInformationJTextPaneDisplay;

/**
 * This notification task is used to inform the user about a non-error situation (e.g. statistics
 * (how many goals have been closed) etc.)
 *
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
