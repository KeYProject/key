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
import java.awt.event.KeyEvent;
import java.io.File;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.utilities.GuiUtilities;

/**
 * Loads the last opened file
 */

public final class OpenMostRecentFileAction extends MainWindowAction {
    
    /**
     * 
     */
    private static final long serialVersionUID = 4855372503837208313L;

    public OpenMostRecentFileAction(MainWindow mainWindow) {
	super(mainWindow);
        setName("Reload");
        setIcon(IconFactory.openMostRecent(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Reload last opened file.");
        setAcceleratorLetter(KeyEvent.VK_R);
    }
    
    public void actionPerformed(ActionEvent e) {
        if (mainWindow.getRecentFiles() != null && 
        	mainWindow.getRecentFiles().getMostRecent() != null) {
            final String recentFile = mainWindow.getRecentFiles().getMostRecent().getAbsolutePath();
            if (recentFile != null) {
                File file = new File(recentFile);
                KeYFileChooser fileChooser =
                        GuiUtilities.getFileChooser("Select file to load proof or problem");
                fileChooser.selectFile(file);
                mainWindow.loadProblem(file);
            }
        }
    }
}