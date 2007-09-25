/*
 * Created on 13.03.2005
 */
package de.uka.ilkd.key.gui.notification.actions;

import java.awt.Component;

import de.uka.ilkd.key.gui.notification.NotificationAction;

/**
 * Actions which display a text should inherit from 
 * this abstract notification action.  
 * @author bubel
 */
public abstract class ShowDisplayPane implements NotificationAction {

    /**
     * the message to be displayed
     */
    private String message = "";
    protected Component parentComponent;
    
    
    /**
     * creates an instance of this action kind
     */
    public ShowDisplayPane(Component parentComponent) {
        this.parentComponent=parentComponent;
    }
    
    /**
     * sets the message to be displayed
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
