
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;

import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
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
	
        setName("Edit Last Opened File");
        setIcon(IconFactory.editFile(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Open the last opened file with the default external editor");
	
        if (!Main.getKeyDesktop().supportsEdit() && !Main.getKeyDesktop().supportsOpen()) {
            setEnabled(false);
        }
        lookupAcceleratorKey();
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
            // WP: see #854: this uses the file registered for "Edit" action in Windows,
            //  which can not be set via GUI.
            //  As far as I know, for Linux/Mac, supportsEdit() always returns false. TODO: check
            // Therefore, we just use the "Open" action now.
            //
            //if (Main.getKeyDesktop().supportsEdit() && file.isFile()) {
            //   Main.getKeyDesktop().edit(file);
            //} else {
            Main.getKeyDesktop().open(file);
            //}
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