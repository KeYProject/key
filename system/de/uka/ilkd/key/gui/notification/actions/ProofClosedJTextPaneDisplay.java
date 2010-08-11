// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
/*
 * Created on 17.03.2005
 */
package de.uka.ilkd.key.gui.notification.actions;

import java.awt.Component;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.gui.notification.events.ProofClosedNotificationEvent;
import de.uka.ilkd.key.proof.Proof;

/**
 * Displays a JOptionPane informing about a closed proof
 * and gives some statistics.
 * @author bubel
 */
public class ProofClosedJTextPaneDisplay extends ShowDisplayPane {
  
    
    public ProofClosedJTextPaneDisplay(Component parentComponent) {
        super(parentComponent);
    }
    /**
     * Displays a JOptionPane informing the user about a closed proof.
     * If available some statistics are displayed as well.
     */
    public boolean execute(NotificationEvent pcne) {               
        if (pcne instanceof ProofClosedNotificationEvent) {
            Proof proof = ((ProofClosedNotificationEvent)pcne).getProof();
            if (proof != null) {
                setMessage("Proved.\nStatistics:\n"+proof.statistics());
            }
        } else {
            setMessage("Proof Closed. No statistics available.");
        }
        JOptionPane.showMessageDialog
            (parentComponent, getMessage(), 
                    "Proof closed", JOptionPane.INFORMATION_MESSAGE);              
        return true;
    }
    
    
}
