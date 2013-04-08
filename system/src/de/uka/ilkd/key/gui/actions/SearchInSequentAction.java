package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.MainWindow;
import java.awt.Toolkit;

/*
 * Menu option for showing the sequent search bar.
 * Keyboard shortcut: STRG+F.
 */
public class SearchInSequentAction extends MainWindowAction {

    public SearchInSequentAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Search in sequent view");
        setTooltip("Search for strings in the current sequent.");
        // Key combination for this action: STRG+F.
        this.setAcceleratorKey(KeyStroke.getKeyStroke(KeyEvent.VK_F,
                Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
        getMediator().enableWhenProofLoaded(this);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        mainWindow.sequentSearchBar.setVisible(true);
    }
}
