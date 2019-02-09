package de.uka.ilkd.key.gui.ext;

import de.uka.ilkd.key.gui.MainWindow;

import javax.swing.*;
import java.util.List;

/**
 * @author weigl
 */
public interface KeYMainMenu {
    String PRIORITY = "PRIORITY";
    String PATH = "PATH";

    List<Action> getActions(MainWindow mainWindow);


    default int getPriority() {
        return 0;
    }
}
