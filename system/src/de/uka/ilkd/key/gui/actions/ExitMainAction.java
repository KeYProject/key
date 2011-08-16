package de.uka.ilkd.key.gui.actions;

import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowListener;

import javax.swing.JOptionPane;
import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.PathConfig;

public class ExitMainAction extends MainWindowAction {
    
    public ExitMainAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("Exit");
	setTooltip("Leave KeY.");
	setAcceleratorLetter(KeyEvent.VK_Q);
    }
    
    public final WindowListener windowListener = new WindowAdapter() {
	public void windowClosing(java.awt.event.WindowEvent e) {
	    exitMain();
	};
    };

    protected void exitMain() {
        boolean quit = false;       
        final int option = JOptionPane.showConfirmDialog
        (mainWindow, "Really Quit?", "Exit", 
                JOptionPane.YES_NO_OPTION);		   	    
        if (option == JOptionPane.YES_OPTION) {
            quit = true;
        } 


        mainWindow.getRecentFiles().store(PathConfig.RECENT_FILES_STORAGE);

        if (quit) {            
            getMediator().fireShutDown(new GUIEvent(this));

            System.out.println("Have a nice day.");
            mainWindow.savePreferences();
            System.exit(-1);
        }
        
        // Release threads waiting for the prover to exit
        synchronized (mainWindow.monitor) {
            mainWindow.monitor.notifyAll();
        }
    }

    @Override
    public void actionPerformed(ActionEvent e) {
	exitMain();
    }

}
