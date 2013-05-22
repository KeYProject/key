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

package de.uka.ilkd.key.gui.notification.actions;

import java.awt.Frame;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.notification.events.ExceptionFailureEvent;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;

public class ExceptionFailureNotificationDialog extends ShowDisplayPane {

	public ExceptionFailureNotificationDialog(Frame parentComponent) {
	    super(parentComponent);
    }

	@Override
	public boolean execute(NotificationEvent event) {
        if (event instanceof ExceptionFailureEvent) {     
        	ExceptionFailureEvent ev = (ExceptionFailureEvent) event;
            setMessage(ev.getErrorMessage());            
    		ExceptionDialog.showDialog(parentComponent, ev.getException());
        } else {
            setMessage("An unknown error has occured." + event);
            JOptionPane.showMessageDialog
            (parentComponent, getMessage(), 
                    "Error", JOptionPane.ERROR_MESSAGE);              
        }
        return true;             
	}

}