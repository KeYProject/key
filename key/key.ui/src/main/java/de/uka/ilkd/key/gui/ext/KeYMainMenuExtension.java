package de.uka.ilkd.key.gui.ext;

import de.uka.ilkd.key.gui.MainWindow;

import javax.swing.*;
import java.util.List;

/**
 *
 * @author Alexander Weigl
 */
public interface KeYMainMenuExtension {
    /**
     *
     * @param mainWindow
     * @return
     */
    List<Action> getMainMenuActions(MainWindow mainWindow);

    /**
     *
     * @return
     */
    default int getPriority() {
        return 0;
    }
}
