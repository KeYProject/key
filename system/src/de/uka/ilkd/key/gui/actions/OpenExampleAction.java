package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.io.File;

import javax.swing.AbstractAction;

import de.uka.ilkd.key.gui.ExampleChooser;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.MainWindow;

/**
 * Opens a file dialog allowing to select the example to be loaded
 */
public final class OpenExampleAction extends MainWindowAction {
    
    public OpenExampleAction(MainWindow mainWindow) {
	super(mainWindow);
        setName("Load Example...");
        setTooltip("Browse and load included examples.");
    }
    
    public void actionPerformed(ActionEvent e) {
        File file = ExampleChooser.showInstance(Main.getExamplesDir());
        if(file != null) {
            mainWindow.loadProblem(file);
        }
    }
}    