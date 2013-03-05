package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.util.GuiUtilities;
import de.uka.ilkd.key.util.MiscTools;

/**
 * Saves the current selected proof.
 */
public final class SaveFileAction extends MainWindowAction {
    
    /**
     * 
     */
    private static final long serialVersionUID = -5479654127272775831L;

    public SaveFileAction(MainWindow mainWindow) {
	super(mainWindow);
        setName("Save ...");
        setIcon(IconFactory.saveFile(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Save current proof.");
        setAcceleratorLetter(KeyEvent.VK_S);
        
        mainWindow.getMediator().enableWhenProofLoaded(this);
    }
    
    public void actionPerformed(ActionEvent e) {
        if (mainWindow.getMediator().ensureProofLoaded()) {
            final KeYFileChooser jFC = GuiUtilities.getFileChooser("Choose filename to save proof");
            
            final String defaultName 
            	= MiscTools.toValidFileName(mainWindow.getMediator().getSelectedProof()
            		                            .name()
            		                            .toString()).toString();
            
            boolean saved = jFC.showSaveDialog(mainWindow, defaultName + ".proof");
            if (saved) {
                mainWindow.saveProof(jFC.getSelectedFile());
            }
        } else {
            mainWindow.popupWarning("No proof.", "Oops...");
        }
    }
}
