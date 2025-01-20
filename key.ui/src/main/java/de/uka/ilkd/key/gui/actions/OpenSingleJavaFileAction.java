/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.io.File;
import java.util.Collections;
import javax.swing.*;

import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.proof.io.ProblemLoader;

/**
 * Offers a loading of a single Java file, without considering the folder as part of a classpath.
 *
 * @author weigl
 *
 * @see OpenFileAction
 */
public class OpenSingleJavaFileAction extends MainWindowAction {
    public OpenSingleJavaFileAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Open Single Java File...");
        // setIcon(IconFactory.openKeYFile(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Browse and load a single Java file without classpath.");
    }

    public void actionPerformed(ActionEvent e) {
        KeYFileChooser fc = KeYFileChooser.getFileChooser("Select a Java file");
        fc.setFileFilter(KeYFileChooser.JAVA_FILTER);

        fc.setAcceptAllFileFilterUsed(false);
        fc.setFileSelectionMode(KeYFileChooser.FILES_ONLY);
        int result = fc.showOpenDialog(mainWindow);


        if (result == JFileChooser.APPROVE_OPTION) {
            File file = fc.getSelectedFile();
            mainWindow.addRecentFile(file.getAbsolutePath());

            WindowUserInterfaceControl ui = mainWindow.getUserInterface();
            ProblemLoader pl = ui.getProblemLoader(file, Collections.emptyList(), null,
                Collections.emptyList(), ui.getMediator());
            pl.setLoadSingleJavaFile(true);
            pl.runAsynchronously();
        }
    }
}
