package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.nodeviews.IncrementalSearch;
import de.uka.ilkd.key.gui.nodeviews.SequentView;

public class SearchInSequentAction extends MainWindowAction {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public SearchInSequentAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Search in sequent view");
        setTooltip("Search for strings in the current sequent.");
        this.setAcceleratorKey(KeyStroke.getKeyStroke(KeyEvent.VK_F3,0));
        
        getMediator().enableWhenProof(this);
    }
	
	@Override
    public void actionPerformed(ActionEvent e) {
		if (mainWindow.getMediator().getProof() != null) {
			SequentView seqView = mainWindow.getSequentView();
                        mainWindow.sequentSearchPanel.toggleVisibility();
			IncrementalSearch search = IncrementalSearch.getInstance();
            if (!search.isInitialised()) {
                search.initSearch(seqView);
            } else {
                search.requestFocus();
            }
		}
		
    }

}
