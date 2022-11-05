package de.uka.ilkd.key.gui.actions;

import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.nodeviews.SequentView;

/*
 * Menu option for showing the sequent search bar. Keyboard shortcut: STRG+F.
 */
public class SearchInSequentAction extends MainWindowAction {

    private static final long serialVersionUID = -9002009635814787502L;

    public SearchInSequentAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Search in Sequent View");
        setIcon(IconFactory.search(16));
        setTooltip("Search for strings in the current sequent.");
        // Key combination for this action: STRG+F.
        this.setAcceleratorKey(KeyStroke.getKeyStroke(KeyEvent.VK_F,
            Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
        getMediator().enableWhenProofLoaded(this);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        SequentView view = mainWindow.sequentViewSearchBar.getSequentView();
        String searchString = view.getHighlightedText();
        mainWindow.sequentViewSearchBar.searchFor(searchString);
    }
}
