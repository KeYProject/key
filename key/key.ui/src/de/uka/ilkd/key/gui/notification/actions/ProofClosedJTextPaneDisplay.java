// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
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

import java.awt.Dimension;
import java.awt.Font;
import java.awt.Frame;

import javax.swing.BorderFactory;
import javax.swing.JEditorPane;
import javax.swing.JOptionPane;
import javax.swing.JScrollPane;
import javax.swing.UIManager;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.ShowProofStatistics;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.gui.notification.events.ProofClosedNotificationEvent;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.Debug;

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
    @Override
   public synchronized boolean execute(NotificationEvent pcne) {               
        if (pcne instanceof ProofClosedNotificationEvent) {
            Proof proof = ((ProofClosedNotificationEvent)pcne).getProof();
            if (proof != null) {
                setMessage(ShowProofStatistics.getHTMLStatisticsMessage(proof));
            }
        } else {
            setMessage("Proof Closed. No statistics available.");
        }
        
        JEditorPane contentPane = new JEditorPane("text/html", getMessage());
        contentPane.setEditable(false);
        contentPane.setBorder(BorderFactory.createEmptyBorder());
        contentPane.setCaretPosition(0);
        contentPane.setBackground(MainWindow.getInstance().getBackground());
        contentPane.setSize(new Dimension(10, 360));
        contentPane.setPreferredSize(new Dimension(contentPane.getPreferredSize().width + 15, 360));
        
        JScrollPane scrollPane = new JScrollPane(contentPane);
        scrollPane.setBorder(BorderFactory.createEmptyBorder());
        
        Font myFont = UIManager.getFont(Config.KEY_FONT_PROOF_TREE);
        if (myFont != null) {
            contentPane.putClientProperty(JEditorPane.HONOR_DISPLAY_PROPERTIES, Boolean.TRUE);
            contentPane.setFont(myFont);
        } else {
            Debug.out("KEY_FONT_PROOF_TREE not available. Use standard font.");
        }
        
        JOptionPane.showMessageDialog
            (parentComponent, scrollPane,
                    "Proof closed", JOptionPane.INFORMATION_MESSAGE);
        
        return true;
    }
}
