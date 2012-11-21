package de.uka.ilkd.key.gui.actions;

import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

import javax.swing.JDialog;
import javax.swing.JOptionPane;
import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.nodeviews.SequentView;
import de.uka.ilkd.key.gui.nodeviews.IncrementalSearch;

public class SearchInSequentAction extends MainWindowAction {

	public SearchInSequentAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Search in sequent view");
        setTooltip("Search for rule names or node numbers in the proof tree.");
        this.setAcceleratorKey(KeyStroke.getKeyStroke(KeyEvent.VK_F3,0));
    }
	
	@Override
    public void actionPerformed(ActionEvent e) {
		if (mainWindow.getMediator().getProof() != null) {
			SequentView seqView = mainWindow.getSequentView();
			IncrementalSearch search = IncrementalSearch.getInstance();
            if (!search.isInitialised()) {
                search.initSearch(seqView);
            } else {
                search.requestFocus();
            }
		}
		
    }

}