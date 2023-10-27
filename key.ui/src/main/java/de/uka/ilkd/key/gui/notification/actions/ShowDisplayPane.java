/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.notification.actions;

import java.awt.Frame;

import de.uka.ilkd.key.gui.notification.NotificationAction;

/**
 * Actions which display a text should inherit from this abstract notification action.
 *
 * @author bubel
 */
public abstract class ShowDisplayPane implements NotificationAction {

    /**
     * the message to be displayed
     */
    private String message = "";
    protected final Frame parentComponent;


    /**
     * creates an instance of this action kind
     */
    public ShowDisplayPane(Frame parentComponent) {
        this.parentComponent = parentComponent;
    }

    /**
     * sets the message to be displayed
     *
     * @param message the String to be displayed
     */
    public void setMessage(String message) {
        this.message = message;
    }

    /**
     * returns the text string displayed by this action
     */
    public String getMessage() {
        return message;
    }

}
