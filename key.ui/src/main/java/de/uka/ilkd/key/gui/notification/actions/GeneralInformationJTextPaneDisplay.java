/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.notification.actions;

import java.awt.Frame;
import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;

/**
 * Displays a string in a {@link javax.swing.JOptionPane} information message window.
 *
 * @author bubel
 */
public class GeneralInformationJTextPaneDisplay extends ShowDisplayPane {

    /**
     */
    public GeneralInformationJTextPaneDisplay(Frame parentComponent) {
        super(parentComponent);
    }

    /**
     * @see de.uka.ilkd.key.gui.notification.NotificationAction#execute(NotificationEvent)
     */
    @Override
    public boolean execute(NotificationEvent event) {
        final String title;
        if (event instanceof GeneralInformationEvent) {
            setMessage(((GeneralInformationEvent) event).getMessage());
            title = ((GeneralInformationEvent) event).getContext();
        } else {
            setMessage("Info: " + event);
            title = "Information";
        }
        JOptionPane.showMessageDialog(parentComponent, getMessage(), title,
            JOptionPane.INFORMATION_MESSAGE);
        return true;
    }

}
