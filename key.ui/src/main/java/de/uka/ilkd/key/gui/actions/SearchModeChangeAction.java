package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.nodeviews.SequentViewSearchBar;


/*
 * Menu option for showing the next search result of sequent search Keyboard shortcut: F3. This
 * shortcut is set in the KeyStrokemanager
 */
public class SearchModeChangeAction extends MainWindowAction {

    private static final long serialVersionUID = -9002019635814787502L;
    private final SequentViewSearchBar searchBar;
    private final SequentViewSearchBar.SearchMode mode;

    public SearchModeChangeAction(MainWindow mainWindow, SequentViewSearchBar searchBar,
            SequentViewSearchBar.SearchMode mode) {
        super(mainWindow);
        setName(mode.toString());

        setIcon(mode.icon);
        setTooltip("Find the next occurence of current search term in sequent.");
        getMediator().enableWhenProofLoaded(this);
        if (mode == SequentViewSearchBar.SearchMode.HIGHLIGHT) {
            setAcceleratorLetter(KeyEvent.VK_H);
        } else if (mode == SequentViewSearchBar.SearchMode.HIDE) {
            setAcceleratorLetter(KeyEvent.VK_ESCAPE);
        } else if (mode == SequentViewSearchBar.SearchMode.REGROUP) {
            setAcceleratorLetter(KeyEvent.VK_I);
        }

        this.searchBar = searchBar;
        this.mode = mode;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        searchBar.setSearchMode(mode);
    }
}
