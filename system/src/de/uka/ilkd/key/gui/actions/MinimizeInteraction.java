package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import javax.swing.JCheckBoxMenuItem;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofSettings;

public class MinimizeInteraction extends MainWindowAction {

    public MinimizeInteraction(MainWindow mainWindow) {
	super(mainWindow);
	setName("Minimize Interaction");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
	boolean b = ((JCheckBoxMenuItem) e.getSource()).isSelected();
	getMediator().setStupidMode(b);
	ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().setTacletFilter(b);
    }

}
