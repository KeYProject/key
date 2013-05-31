// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


/*
 * Created on 13.03.2005
 */
package de.uka.ilkd.key.gui.notification.actions;

import java.awt.Frame;

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
    protected Frame parentComponent;
    
    
    /**
     * creates an instance of this action kind
     */
    public ShowDisplayPane(Frame parentComponent) {
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
