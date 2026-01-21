package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

import java.awt.event.ActionEvent;

/*
 * Menu option for showing the next search result of sequent search Keyboard shortcut: F3. This
 * shortcut is set in the KeyStrokemanager
 */
public class SearchNextAction extends MainWindowAction {

    private static final long serialVersionUID = -9002009635814787502L;

    public SearchNextAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Find Next Occurrence");
        setIcon(IconFactory.SEARCH_NEXT.get(16));
        setTooltip("Find the next occurrence of current search term in sequent.");
        getMediator().enableWhenProofLoaded(this);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        mainWindow.sequentViewSearchBar.searchNext();
    }
}
