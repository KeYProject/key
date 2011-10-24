package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.io.File;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;

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
        setName("Reload ");
        setIcon(IconFactory.openMostRecent(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Reload last opened file.");
        setAcceleratorLetter(KeyEvent.VK_R);
    }
    
    public void actionPerformed(ActionEvent e) {
        if (mainWindow.getRecentFiles() != null && 
        	mainWindow.getRecentFiles().getMostRecent() != null) {
            final String recentFile = mainWindow.getRecentFiles().getMostRecent().getAbsolutePath();
            if (recentFile != null) {
                mainWindow.loadProblem(new File(recentFile));
            }
        }
    }
}    