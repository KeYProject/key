package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import de.uka.ilkd.key.gui.MainWindow;

/*
 * Menu option for showing the proof tree search bar.
 * Keyboard shortcut: STRG+SHIFT+F.
 */

public class SearchInProofTreeAction extends MainWindowAction {

    private static final long serialVersionUID = -3317991560912504404L;

    public SearchInProofTreeAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Search in proof tree");
        setTooltip("Search for rule names or node numbers in the proof tree.");
        
        this.setAcceleratorKey(
                de.uka.ilkd.key.gui.prooftree.ProofTreeView.searchKeyStroke);
        getMediator().enableWhenProofLoaded(this);
        
    }

    @Override
    public void actionPerformed(ActionEvent arg0) {
        mainWindow.selectTab(0);
        mainWindow.getProofView().showSearchPanel();
    }
}
