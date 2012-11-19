package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import javax.swing.JOptionPane;
import javax.swing.JTextArea;
import javax.swing.text.JTextComponent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.proof.Proof;

public class ShowActiveTactletOptionsAction extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = -7012564698194718532L;

    public ShowActiveTactletOptionsAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("Show Active Taclet Options...");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
	showActivatedChoices();
    }

    private void showActivatedChoices() {
        Proof currentProof = getMediator().getProof();
        if (currentProof == null) {
            mainWindow.notify(new GeneralInformationEvent("No Options available.",
                    "If you wish to see Taclet Options "
                    + "for a proof you have to load one first"));
        } else {
            String message = "Active Taclet Options:\n";
	    int rows = 0;
	    int columns = 0;
            for (final String choice : currentProof.getSettings().
                    getChoiceSettings().getDefaultChoices().values()) {
                message += choice + "\n";
		rows++;
		if (columns < choice.length()) {
			columns = choice.length();
		}
            }
            final JTextComponent activeOptions = new JTextArea(message, rows, columns);
            activeOptions.setEditable(false);
            JOptionPane.showMessageDialog(mainWindow, activeOptions, "Active Taclet Options",
                    JOptionPane.INFORMATION_MESSAGE);
        }
    }
}
