/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.io.File;

import de.uka.ilkd.key.gui.MainWindow;

/**
 * Load the file saved at the location described by {@link QuickSaveAction}. Use the F6 key to
 * access this feature.
 *
 * @author daniel
 *
 */
public class QuickLoadAction extends MainWindowAction {
    private static final long serialVersionUID = -7149996409297248408L;

    /**
     * Create a new action.
     *
     * @param mainWindow the main window.
     */
    public QuickLoadAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Quickload");
        setTooltip("Load previously quicksaved file");
    }

    /**
     * Load the file saved at the location described by
     * {@link QuickSaveAction#quickSave(MainWindow)}.
     *
     * @param mainWindow the main window.
     */
    public static void quickLoad(MainWindow mainWindow) {
        final String filename = QuickSaveAction.QUICK_SAVE_PATH;
        mainWindow.loadProblem(new File(filename));
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        quickLoad(mainWindow);
    }
}
