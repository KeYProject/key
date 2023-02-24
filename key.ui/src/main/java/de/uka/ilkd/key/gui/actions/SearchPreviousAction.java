package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import java.awt.event.ActionEvent;


/*
 * Menu option for showing the next search result Keyboard shortcut: F3. This shortcut is set in the
 * KeyStrokemanager
 */
public class SearchPreviousAction extends MainWindowAction {

    private static final long serialVersionUID = -9002009635814787502L;

    public SearchPreviousAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Find Previous Occurrence");
        setIcon(IconFactory.SEARCH_PREV.get(16));
        setTooltip("Find the previous occurrence of current search term in sequent.");
        getMediator().enableWhenProofLoaded(this);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        mainWindow.sequentViewSearchBar.searchPrevious();
    }
}
