/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.extension.api;

import java.util.Collections;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;

public interface KeYToolbarExtensionAdapter extends KeYGuiExtension.Toolbar {
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
