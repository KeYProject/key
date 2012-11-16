package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ChoiceSelector;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;

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
        if (getMediator().getProof() == null) {
            mainWindow.notify(
                    new GeneralInformationEvent(
                            "No contracts available.",
                            "If you wish to see the available options "
                            + "for a proof, you have to load one first."));
        } else {
            new ChoiceSelector
            (ProofSettings.DEFAULT_SETTINGS.getChoiceSettings());
        }
    }

}
