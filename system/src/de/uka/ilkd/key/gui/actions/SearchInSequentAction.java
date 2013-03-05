package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.MainWindow;

/*
 * Menu option, to show the sequent search bar.
 * Can also be triggered by "F3".
 */
public class SearchInSequentAction extends MainWindowAction {

    public SearchInSequentAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Search in sequent view");
        setTooltip("Search for strings in the current sequent.");
        this.setAcceleratorKey(KeyStroke.getKeyStroke(KeyEvent.VK_F3, 0));
        getMediator().enableWhenProofLoaded(this);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        mainWindow.sequentSearchBar.setVisible(true);
    }
}
