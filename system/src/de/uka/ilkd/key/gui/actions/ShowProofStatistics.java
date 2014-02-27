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
import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.Pair;

public class ShowProofStatistics extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = -8814798230037775905L;

    public ShowProofStatistics(MainWindow mainWindow) {
	super(mainWindow);
	setName("Show Proof Statistics...");
        setIcon(IconFactory.statistics(16));
	
	getMediator().enableWhenProofLoaded(this);

    }

    @Override
    public void actionPerformed(ActionEvent e) {
        final Proof proof = getMediator().getSelectedProof();
        if(proof == null) {
            mainWindow.notify(new GeneralInformationEvent("No statistics available.",
                    "If you wish to see the statistics "
                            + "for a proof you have to load one first"));
        } else {

            final int openGoals = proof.openGoals().size();
            String stats = (openGoals > 0)? ""+openGoals+" open goals.": "Closed.";
            stats += "\n\n";
            for (Pair<String,String> x: proof.statistics().getSummary()) {
                if ("".equals(x.second)) stats +="\n";
                stats += x.first+": "+ x.second+"\n";
            }


            JOptionPane.showMessageDialog(mainWindow, 
                    stats,
                    "Proof Statistics", JOptionPane.INFORMATION_MESSAGE);
        }
    }


}
