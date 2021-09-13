// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.proof.io.ProblemLoader;

import javax.swing.*;
import javax.swing.filechooser.FileFilter;
import java.awt.event.ActionEvent;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.io.File;
import java.util.Collections;

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
        //setIcon(IconFactory.openKeYFile(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Browse and load a single Java file without classpath.");
        setAcceleratorKey(KeyStroke.getKeyStroke(KeyEvent.VK_O, InputEvent.CTRL_DOWN_MASK));
        lookupAcceleratorKey();
    }

    public void actionPerformed(ActionEvent e) {
        KeYFileChooser keYFileChooser = new KeYFileChooser(Main.getWorkingDir());
        JFileChooser jfc = keYFileChooser.getFileChooser();
        jfc.setDialogTitle("Select a Java file");
        jfc.setFileFilter(new FileFilter() {
            @Override
            public boolean accept(File f) {
                return f.getName().endsWith(".java") || f.isDirectory();
            }

            @Override
            public String getDescription() {
                return "Java Source Files";
            }
        });
        jfc.setAcceptAllFileFilterUsed(false);
        jfc.setFileSelectionMode(JFileChooser.FILES_ONLY);
        int result = jfc.showOpenDialog(mainWindow);


        if (result == JFileChooser.APPROVE_OPTION) {
            File file = keYFileChooser.getSelectedFile();
            mainWindow.addRecentFile(file.getAbsolutePath());

            WindowUserInterfaceControl ui = mainWindow.getUserInterface();
            ProblemLoader pl = ui.getProblemLoader(file,
                    Collections.emptyList(), null, Collections.emptyList(),
                    ui.getMediator());
            pl.setLoadSingleJavaFile(true);
            pl.runAsynchronously();
        }
    }
}