/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.io.File;

import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.ExampleChooser;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

/**
 * Opens a file dialog allowing to select the example to be loaded
 */
public final class OpenExampleAction extends MainWindowAction {

    /**
     *
     */
    private static final long serialVersionUID = -7703620988220254791L;

    public OpenExampleAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Load Example...");
        setIcon(IconFactory.openExamples(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Browse and load included examples.");
    }

    public void actionPerformed(ActionEvent e) {
        File file = ExampleChooser.showInstance(Main.getExamplesDir());
        if (file != null) {
            KeYFileChooser.getFileChooser("Select file to load").setSelectedFile(file);
            mainWindow.loadProblem(file);
        }
    }
}
