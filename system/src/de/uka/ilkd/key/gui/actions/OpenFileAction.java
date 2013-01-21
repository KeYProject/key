package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.io.File;

import javax.swing.JCheckBox;
import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.util.GuiUtilities;

import de.uka.ilkd.key.gui.configuration.FileOpenNotification;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.gui.configuration.ViewSelector;

public class OpenFileAction extends MainWindowAction {
    
    /**
     * 
     */
    private static final long serialVersionUID = -8548805965130100236L;

    public OpenFileAction(MainWindow mainWindow) {
	super(mainWindow);
        setName("Load...");
        setIcon(IconFactory.openKeYFile(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Browse and load problem or proof files.");
        setAcceleratorLetter(KeyEvent.VK_O);
    }
    
    public void actionPerformed(ActionEvent e) {
    	if (ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getNotifyLoadBehaviour()) {
    		FileOpenNotification notification = new FileOpenNotification(mainWindow);
    		notification.setVisible(true);
    		
            JCheckBox checkbox = new JCheckBox("Don't show this warning again");
            Object[] message = { "When you load a Java file, all java files in the current",
                    "directory and all subdirectories will be loaded as well.",
                    checkbox };
            JOptionPane.showMessageDialog(mainWindow, message, 
                    "Please note", JOptionPane.WARNING_MESSAGE);
            System.out.println(checkbox.isSelected());
    	}
    	
    	
        KeYFileChooser keYFileChooser = 
            GuiUtilities.getFileChooser("Select file to load proof or problem");
        
        boolean loaded = keYFileChooser.showOpenDialog(mainWindow);
        
        if (loaded) {
            File file = keYFileChooser.getSelectedFile();
            mainWindow.loadProblem(file);
        }
        
    }
}