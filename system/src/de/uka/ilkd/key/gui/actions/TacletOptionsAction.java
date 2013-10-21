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
import java.awt.event.KeyEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ChoiceSelector;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;

public class TacletOptionsAction extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = -6813540362001480606L;

    public TacletOptionsAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("Taclet Options...");
	setAcceleratorLetter(KeyEvent.VK_T);
	
	getMediator().enableWhenProofLoaded(this);

    }

    @Override
    public void actionPerformed(ActionEvent e) {
        if (getMediator().getSelectedProof() == null) {
            mainWindow.notify(
                    new GeneralInformationEvent(
                            "No contracts available.",
                            "If you wish to see the available options "
                            + "for a proof, you have to load one first."));
        } else {
            new ChoiceSelector
            (ProofSettings.DEFAULT_SETTINGS.getChoiceSettings());
        }
    }

}
