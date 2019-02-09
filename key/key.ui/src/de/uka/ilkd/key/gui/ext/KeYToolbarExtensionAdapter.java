package de.uka.ilkd.key.gui.ext;

import de.uka.ilkd.key.gui.MainWindow;

import javax.swing.*;
import java.util.Collections;
import java.util.List;

public interface KeYToolbarExtensionAdapter extends KeYToolbarExtension {
    /**
     * @param mainWindow
     * @return
     */
    default List<Action> getToolbarActions(MainWindow mainWindow) {
        return Collections.emptyList();
    }

    @Override
    default JToolBar getToolbar(MainWindow mainWindow) {
        JToolBar tb = new JToolBar(getClass().getName());
        getToolbarActions(mainWindow).forEach(tb::add);
        return tb;
    }
}
