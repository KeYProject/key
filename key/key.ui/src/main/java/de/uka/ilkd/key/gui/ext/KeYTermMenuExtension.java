package de.uka.ilkd.key.gui.ext;

import de.uka.ilkd.key.gui.MainWindow;

import javax.swing.*;
import java.util.List;

/**
 * @author Alexander Weigl <weigl@kit.edu>
 */
public interface KeYTermMenuExtension {
    /**
     * @param mainWindow non-null
     * @return a list of actions
     */
    List<Action> getTermMenuActions(MainWindow mainWindow);
}
