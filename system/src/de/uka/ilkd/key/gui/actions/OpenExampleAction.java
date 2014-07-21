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

package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.io.File;

import de.uka.ilkd.key.gui.ExampleChooser;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.MainWindow;

/**
 * Opens a file dialog allowing to select the example to be loaded
 */
public final class OpenExampleAction extends MainWindowAction {
    
    /**
     * 
     */
    private static final long serialVersionUID = -7703620988220254791L;

    public OpenExampleAction(MainWindow mainWindow) {
	super(mainWindow);
        setName("Load Example");
        setTooltip("Browse and load included examples.");
    }
    
    public void actionPerformed(ActionEvent e) {
        File file = ExampleChooser.showInstance(Main.getExamplesDir());
        if(file != null) {
            mainWindow.loadProblem(file);
        }
    }
}