package de.uka.ilkd.key.gui.actions;

import java.awt.Desktop;
import java.awt.event.ActionEvent;
import java.io.File;

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
	
	setName("Edit");
	setIcon(IconFactory.editFile(MainWindow.TOOLBAR_ICON_SIZE));
	setTooltip("Edit last opened file.");
	
	if (!Desktop.isDesktopSupported()
	        || (!Desktop.getDesktop().isSupported(Desktop.Action.EDIT) && !Desktop
	                .getDesktop().isSupported(Desktop.Action.OPEN))) {
	    setEnabled(false);
	}
    }

    public void actionPerformed(ActionEvent e) {
	if (mainWindow.getRecentFiles() != null
	        && mainWindow.getRecentFiles().getMostRecent() != null) {
	    Desktop d = Desktop.getDesktop();
	    final String recentFile = mainWindow.getRecentFiles()
		    .getMostRecent().getAbsolutePath();
	    if (recentFile != null) {
		File f = new File(recentFile);
		try {
		    if (d.isSupported(Desktop.Action.EDIT) && f.isFile()) {
			d.edit(f);
		    } else {
			d.open(f);
		    }
		} catch (Exception exc) {
		    setEnabled(false);
		}
	    }
	}
    }
}
