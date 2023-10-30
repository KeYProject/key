/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.notification.actions;

import java.awt.Frame;
import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;

/**
 * Displays a string in a {@link javax.swing.JOptionPane} error message window.
 *
 * @author bubel
 */
public class GeneralFailureJTextPaneDisplay extends ShowDisplayPane {

    /**
     * generates an action used for displaying text
     */
    public GeneralFailureJTextPaneDisplay(Frame parentComponent) {
        super(parentComponent);

    }

    /*
     * (non-Javadoc)
     *
     * @see
     * de.uka.ilkd.key.gui.notification.NotificationAction#execute(de.uka.ilkd.key.gui.notification.
     * events.NotificationEvent)
     */
    @Override
    public boolean execute(NotificationEvent event) {
        if (event instanceof GeneralFailureEvent) {
            setMessage(((GeneralFailureEvent) event).getErrorMessage());
        } else {
            setMessage("An unknown error has occured.");
        }
        JOptionPane.showMessageDialog(parentComponent, getMessage(), "Error",
            JOptionPane.ERROR_MESSAGE);
        return true;
    }
}
