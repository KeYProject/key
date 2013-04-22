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

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ViewSelector;

public class ToolTipOptionsAction extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = -360744615149278733L;

    public ToolTipOptionsAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("ToolTip options");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
	 ViewSelector vselector = new ViewSelector(mainWindow);
	 vselector.setVisible(true);
    }

}