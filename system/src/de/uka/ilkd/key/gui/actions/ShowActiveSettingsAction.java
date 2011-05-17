package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import javax.swing.Action;
import javax.swing.Icon;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofSettings;

/**
 * for debugging - opens a window with the settings from current Proof and the
 * default settings
 */
public class ShowActiveSettingsAction extends MainWindowAction {

    public ShowActiveSettingsAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("Show Active Settings...");
    }

    @Override
    public void actionPerformed(ActionEvent e) {

	String message;

	message = "Default Settings: \n"
	        + ProofSettings.DEFAULT_SETTINGS.settingsToString()
	        + "\n----------\n";
	message += "Settings[CurrentProof]:\n"
	        + ((getMediator().getProof() == null) ? "No proof loaded."
	                : getMediator().getProof().getSettings()
	                        .settingsToString());

	final JTextArea settings = new JTextArea(message, 30, 80);
	settings.setEditable(false);
	settings.setLineWrap(true);

	JScrollPane settingsPane = new JScrollPane(settings);

	JOptionPane.showMessageDialog(mainWindow, settingsPane, "Settings",
	        JOptionPane.INFORMATION_MESSAGE);
    }

}
