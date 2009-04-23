// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
/*
 * Created on 18.03.2005
 */
package de.uka.ilkd.key.gui.notification.actions;

import java.awt.Component;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;

/**
 * Displays a string in a {@link javax.swing.JOptionPane} error message window.   
 * @author bubel
 */
public class GeneralFailureJTextPaneDisplay extends ShowDisplayPane {

    /**
     * generates an action used for displaying text 
     */
    public GeneralFailureJTextPaneDisplay(Component parentComponent) {
        super(parentComponent);
        
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.gui.notification.NotificationAction#execute(de.uka.ilkd.key.gui.notification.events.NotificationEvent)
     */
    public boolean execute(NotificationEvent event) {
        if (event instanceof GeneralFailureEvent) {          
            setMessage(((GeneralFailureEvent)event).getErrorMessage());            
        } else {
            setMessage("An unknown error has occured.");
        }
        JOptionPane.showMessageDialog
            (parentComponent, getMessage(), 
                    "Error", JOptionPane.ERROR_MESSAGE);              
        return true;     
    }   
}
