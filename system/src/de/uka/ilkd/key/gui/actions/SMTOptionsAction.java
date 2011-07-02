package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.configuration.SettingsListener;
import de.uka.ilkd.key.gui.smt.ProofDependentSettings;
import de.uka.ilkd.key.gui.smt.ProofIndependentSMTSettings;
import de.uka.ilkd.key.gui.smt.SettingsDialog;
import de.uka.ilkd.key.gui.smt.SettingsModel;
import de.uka.ilkd.key.proof.Proof;


/**
 * creates a menu allowing to choose the external prover to be used
 */
public class SMTOptionsAction extends MainWindowAction {
        private static final long serialVersionUID = 1L;

public SMTOptionsAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("SMT Solvers...");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
            ProofDependentSettings pdSettings = ProofSettings.DEFAULT_SETTINGS.getSMTSettings();
            Proof proof = this.getMediator().getProof();
            if(proof != null){
                    pdSettings = proof.getSettings().getSMTSettings();
            }
            SettingsListener listener = new SettingsListener(){

                @Override
                public void settingsChanged(GUIEvent event) {
                        if(event.getSource() instanceof ProofIndependentSMTSettings ||
                                event.getSource() instanceof ProofDependentSettings)
                        mainWindow.updateSMTSelectMenu();
                }
                    
            };
            ProofIndependentSMTSettings piSettings = ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings();
            pdSettings.addSettingsListener(listener);
            piSettings.addSettingsListener(listener);
            SettingsDialog.INSTANCE.showDialog(new SettingsModel(pdSettings, piSettings, proof));
    }

}
