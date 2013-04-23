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

package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.proof.Proof;

public class ShowProofStatistics extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = -8814798230037775905L;

    public ShowProofStatistics(MainWindow mainWindow) {
	super(mainWindow);
	setName("Show Proof Statistics...");
	
	getMediator().enableWhenProof(this);

    }

    @Override
    public void actionPerformed(ActionEvent e) {
	final Proof proof = getMediator().getSelectedProof();
        if(proof == null) {
            mainWindow.notify(new GeneralInformationEvent("No statistics available.",
                    "If you wish to see the statistics "
                    + "for a proof you have to load one first"));
        } else {
	    final String stats = proof.statistics();


	    JOptionPane.showMessageDialog(mainWindow, 
		    stats,
		    "Proof Statistics", JOptionPane.INFORMATION_MESSAGE);
	}
    }
    

}