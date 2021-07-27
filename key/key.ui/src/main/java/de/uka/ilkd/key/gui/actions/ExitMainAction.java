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

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowListener;
import java.util.EventObject;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

public class ExitMainAction extends MainWindowAction {
   /**
    * If it is {@code true} the whole application is exited via
    * {@link System#exit(int)}. If it is {@code false} the main window is
    * only closed and the application will be still alive.
    */
   public static boolean exitSystem = true;

    /**
     *
     */
   private static final long serialVersionUID = 5881706859613947592L;

   public ExitMainAction(MainWindow mainWindow) {
       super(mainWindow);
       setName("Exit");
       setIcon(IconFactory.quit(16));
       setTooltip("Leave KeY.");
       setAcceleratorLetter(KeyEvent.VK_Q);
       lookupAcceleratorKey();
   }

   public final WindowListener windowListener = new WindowAdapter() {
       @Override
       public void windowClosing(java.awt.event.WindowEvent e) {
           exitMain();
       }
   };

   protected void exitMain() {
       final ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
       if (vs.confirmExit()) {
           final int option = JOptionPane.showConfirmDialog
                   (mainWindow, "Really Quit?\n", "Exit",
                           JOptionPane.YES_NO_OPTION);
           if (option == JOptionPane.YES_OPTION) {
               exitMainWithoutInteraction();
           }
       } else {
           exitMainWithoutInteraction();
       }
   }
   
   
    /**
     * makes all GUI settings persistence; this method is also called by the Eclipse
     * integration to store the settings   
     */
    public void saveSettings() {
       mainWindow.savePreferences(mainWindow);
       mainWindow.syncPreferences();
    }

    /**
     * <p>
     * This method closes the main window directly without asking
     * the user.
     * </p>
     * <p>
     * This functionality must be available separate for developers
     * because for instance the Eclipse integration has to close the
     * main window when Eclipse is closed.
     * </p>
     */
    public void exitMainWithoutInteraction() {
        mainWindow.getRecentFiles().store(PathConfig.getRecentFileStorage());
        getMediator().fireShutDown(new EventObject(this));

        System.out.println("Have a nice day.");
        saveSettings();
        if (exitSystem) {
           //weigl: change to 0, so no error is shown in gradle run
           System.exit(0);
        }
        else {
            mainWindow.setVisible(false);
        }
    }

    @Override
    public void actionPerformed(ActionEvent e) {
	exitMain();
    }

}
