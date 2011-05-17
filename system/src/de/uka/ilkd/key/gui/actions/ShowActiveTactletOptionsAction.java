package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import javax.swing.JOptionPane;
import javax.swing.JTextArea;
import javax.swing.text.JTextComponent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.proof.Proof;

public class ShowActiveTactletOptionsAction extends MainWindowAction {

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
            getMediator()
            .notify(new GeneralInformationEvent("No Options available.",
                    "If you wish to see Taclet Options "
                    + "for a proof you have to load one first"));
        } else {
            String message = "Active Taclet Options:\n";
            for (final String choice : currentProof.getSettings().
                    getChoiceSettings().getDefaultChoices().values()) {
                message += choice + "\n";
            }
            final JTextComponent activeOptions = new JTextArea(message);
            activeOptions.setEditable(false);
            JOptionPane.showMessageDialog(mainWindow, activeOptions, "Active Taclet Options",
                    JOptionPane.INFORMATION_MESSAGE);
        }
    }
}
