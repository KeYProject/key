package de.uka.ilkd.key.gui.ext;

import de.uka.ilkd.key.gui.MainWindow;

import javax.swing.*;

public interface KeYToolbarExtension {
    /**
     * @return
     */
    default int getPriority() {
        return 0;
    }

    JToolBar getToolbar(MainWindow mainWindow);
}
