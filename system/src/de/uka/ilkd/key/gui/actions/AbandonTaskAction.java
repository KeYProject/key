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
import de.uka.ilkd.key.gui.IconFactory;

public final class AbandonTaskAction extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = 915588190956945751L;

    public AbandonTaskAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("Abandon");
        setIcon(IconFactory.abandon(16));
	setAcceleratorLetter(KeyEvent.VK_W);
	setTooltip("Drop current proof.");

	getMediator().enableWhenProofLoaded(this);
    }

    public synchronized void actionPerformed(ActionEvent e) {
    	boolean removalConfirmed =
                getMediator().getUI().confirmTaskRemoval("Are you sure?");
        if (removalConfirmed) {
            getMediator().getUI().removeProof(getMediator().getSelectedProof());
        }
    }
    
}
