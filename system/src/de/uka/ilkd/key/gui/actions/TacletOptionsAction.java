package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ChoiceSelector;
import de.uka.ilkd.key.gui.configuration.ProofSettings;

public class TacletOptionsAction extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = -6813540362001480606L;

    public TacletOptionsAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("Taclet Options...");
	setAcceleratorLetter(KeyEvent.VK_T);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
	new ChoiceSelector
	    (ProofSettings.DEFAULT_SETTINGS.getChoiceSettings());
    }

}
