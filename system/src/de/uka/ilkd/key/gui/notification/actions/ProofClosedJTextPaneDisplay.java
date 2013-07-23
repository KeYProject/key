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
 * Created on 17.03.2005
 */
package de.uka.ilkd.key.gui.notification.actions;

import java.awt.Frame;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.gui.notification.events.ProofClosedNotificationEvent;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.Pair;

/**
 * Displays a JOptionPane informing about a closed proof
 * and gives some statistics.
 * @author bubel
 */
public class ProofClosedJTextPaneDisplay extends ShowDisplayPane {
  
    
    public ProofClosedJTextPaneDisplay(Frame parentComponent) {
        super(parentComponent);
    }
    /**
     * Displays a JOptionPane informing the user about a closed proof.
     * If available some statistics are displayed as well.
     */
    public synchronized boolean execute(NotificationEvent pcne) {               
        if (pcne instanceof ProofClosedNotificationEvent) {
            Proof proof = ((ProofClosedNotificationEvent)pcne).getProof();
            if (proof != null) {
                String statistics = "";
                for (Pair<String, String> x: proof.statistics().getSummary()) {
                    if ("".equals(x.second)) statistics += "\n";
                    statistics += x.first+": "+ x.second+"\n";
                }
                setMessage("Proved.\n\nStatistics:\n"+statistics);
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
