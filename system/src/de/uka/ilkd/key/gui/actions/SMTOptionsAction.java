package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.smt.SettingsDialog;
import de.uka.ilkd.key.gui.smt.TemporarySettings;

/**
 * creates a menu allowing to choose the external prover to be used
 */
public class SMTOptionsAction extends MainWindowAction {

    public SMTOptionsAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("SMT Solvers...");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
	 SettingsDialog.INSTANCE.showDialog(TemporarySettings.getInstance(
		       ProofSettings.DEFAULT_SETTINGS.getSMTSettings()));
    }

}
