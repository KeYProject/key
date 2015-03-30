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

import java.awt.Desktop;
import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;


/**
 * Opens the last opened file in an editor (well, it tries)
 */
public final class EditMostRecentFileAction extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = -6214327707255790570L;

    public EditMostRecentFileAction(MainWindow mainWindow) {
	super(mainWindow);
	
	setName("Edit last opened file");
	setIcon(IconFactory.editFile(MainWindow.TOOLBAR_ICON_SIZE));
	setTooltip("Open the last opened file with the default external editor");
	
	if (!Desktop.isDesktopSupported()
	        || (!Desktop.getDesktop().isSupported(Desktop.Action.EDIT) && !Desktop
	                .getDesktop().isSupported(Desktop.Action.OPEN))) {
	    setEnabled(false);
	}
    }

    public void actionPerformed(ActionEvent e) {
	if (mainWindow.getRecentFiles() != null
	        && mainWindow.getRecentFiles().getMostRecent() != null) {
	    final String recentFile = mainWindow.getRecentFiles()
		    .getMostRecent().getAbsolutePath();
	    if (recentFile != null) {
		File f = new File(recentFile);
	        try {
	            EditFileActionHandler.getInstance().workWithFile(f);
	        } catch (Exception exc) {
	            setEnabled(false);
	        }
	    }
	}
    }
    
    /**
     * <p>
     * The method {@link #workWithFile(File)} of the default instance
     * {@link #getInstance()} is used by {@link EditMostRecentFileAction}
     * to edit the last opened file or to open the last used directory.
     * </p>
     * <p>
     * The advantage of this class is, that it is possible to exchange
     * the implementation. This is for instance done in the Eclipse integration
     * where files are opened inside Eclipse instead of the system editors.
     * </p>
     * @author Martin Hentschel
     */
    public static class EditFileActionHandler {
        /**
         * The default instance.
         */
        public static EditFileActionHandler instance = new EditFileActionHandler();

        /**
         * Opens the given file in the default editor or opens the
         * given directory.
         * @param file The file to edit or the folder to open.
         * @throws IOException Occurred Exception.
         */
        public void workWithFile(File file) throws IOException {
            Desktop d = Desktop.getDesktop();
            if (d.isSupported(Desktop.Action.EDIT) && file.isFile()) {
                d.edit(file);
            } else {
                d.open(file);
            }
        }
        
        /**
         * Returns the default instance.
         * @return The default instance.
         */
        public static EditFileActionHandler getInstance() {
            return instance;
        }

        /**
         * Sets the default instance.
         * @param instance The default instance to set.
         */
        public static void setInstance(EditFileActionHandler instance) {
            EditFileActionHandler.instance = instance;
        }
    }
}