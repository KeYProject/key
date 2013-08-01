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
import javax.swing.JTextArea;
import javax.swing.text.JTextComponent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.proof.Proof;

public class ShowActiveTactletOptionsAction extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = -7012564698194718532L;

    public ShowActiveTactletOptionsAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("Show Active Taclet Options...");
	
	getMediator().enableWhenProofLoaded(this);

    }

    @Override
    public void actionPerformed(ActionEvent e) {
	showActivatedChoices();
    }

    private void showActivatedChoices() {
        Proof currentProof = getMediator().getSelectedProof();
        if (currentProof == null) {
            mainWindow.notify(new GeneralInformationEvent("No Options available.",
                    "If you wish to see Taclet Options "
                    + "for a proof you have to load one first"));
        } else {
            String message = "Active Taclet Options:\n";
            int rows = 0;
			int columns = 0;
			for (final String choice : currentProof.getSettings().
                    getChoiceSettings().getDefaultChoices().values()) {
				message += choice + "\n";
				rows++;
				if (columns < choice.length()) {
					columns = choice.length();
				}
			}
			final JTextComponent activeOptions = new JTextArea(message, rows, columns);
			activeOptions.setEditable(false);
			Object[] toDisplay = {activeOptions,
					"These options can be changed in Options->Taclet Options"
			};
			JOptionPane.showMessageDialog(mainWindow, toDisplay,
					"Taclet Options used in the current proof",
					JOptionPane.INFORMATION_MESSAGE);
		}
    }
}
