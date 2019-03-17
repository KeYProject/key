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

import de.uka.ilkd.key.gui.MainWindow;

/**
 * Load the file saved at the location described by QuickSaveAction.
 * Use the F6 key to access this feature.
 * @author daniel
 *
 */
public class QuickLoadAction extends MainWindowAction {

    private static final long serialVersionUID = 1398506722086997458L;

    public QuickLoadAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Quickload");
//        setIcon(IconFactory.openKeYFile(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Load previously quicksaved file");
    }

    public void actionPerformed(ActionEvent e) {
        final String filename = QuickSaveAction.QUICK_SAVE_PATH;
        mainWindow.loadProblem(new File(filename));
    }
}