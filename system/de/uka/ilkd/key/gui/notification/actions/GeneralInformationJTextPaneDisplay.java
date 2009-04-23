// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
/*
 * Created on 30.03.2005
 */
package de.uka.ilkd.key.gui.notification.actions;

import java.awt.Component;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;

/**
 * Displays a string in a {@link javax.swing.JOptionPane} information 
 * message window.
 * @author bubel
 */
public class GeneralInformationJTextPaneDisplay extends ShowDisplayPane{

    /**
     */
    public GeneralInformationJTextPaneDisplay(Component parentComponent) {
        super(parentComponent);
    }

    /** 
     * @see 
     * de.uka.ilkd.key.gui.notification.NotificationAction#execute(NotificationEvent)
     */
    public boolean execute(NotificationEvent event) {       
        final String title;
        if (event instanceof GeneralInformationEvent) {          
            setMessage(((GeneralInformationEvent)event).getMessage());            
            title = ((GeneralInformationEvent)event).getContext();
        } else {
            setMessage("Info: " + event);
            title = "Information";
        }
        JOptionPane.showMessageDialog
            (parentComponent, getMessage(), 
                    title, JOptionPane.INFORMATION_MESSAGE);              
        return true;      
    }

}
