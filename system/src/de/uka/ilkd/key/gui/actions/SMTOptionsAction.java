// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.EventObject;

import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JLabel;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.configuration.SettingsListener;
import de.uka.ilkd.key.gui.smt.SMTSettingsModel;
import de.uka.ilkd.key.gui.smt.SettingsDialog;
import de.uka.ilkd.key.gui.smt.ProofDependentSMTSettings;
import de.uka.ilkd.key.gui.smt.ProofIndependentSMTSettings;
import de.uka.ilkd.key.gui.smt.SMTSettings;
import de.uka.ilkd.key.gui.testgen.TestGenerationSettings;
import de.uka.ilkd.key.proof.Proof;


/**
 * creates a menu allowing to choose the external prover to be used
 */
public class SMTOptionsAction extends MainWindowAction {
        private static final long serialVersionUID = 1L;

public SMTOptionsAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("SMT Solvers Options");
        setIcon(IconFactory.toolbox(16));
    }

    @Override
    public void actionPerformed(ActionEvent e) {
            ProofDependentSMTSettings pdSettings = ProofSettings.DEFAULT_SETTINGS.getSMTSettings();
            Proof proof = this.getMediator().getSelectedProof();
            if(proof != null){
                    pdSettings = proof.getSettings().getSMTSettings();
            }
            SettingsListener listener = new SettingsListener(){

                @Override
                public void settingsChanged(EventObject event) {
                        if(event.getSource() instanceof ProofIndependentSMTSettings ||
                                event.getSource() instanceof ProofDependentSMTSettings)
                        mainWindow.updateSMTSelectMenu();
                }
                    
            };
            ProofIndependentSMTSettings piSettings = ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings();
            pdSettings.addSettingsListener(listener);
            piSettings.addSettingsListener(listener);
            JComponent bottomComponent = null;
            
            TestGenerationSettings tgSettings = ProofIndependentSettings.DEFAULT_INSTANCE.getTestGenerationSettings();
         
            final SMTSettingsModel settingsModel = new SMTSettingsModel(new SMTSettings(pdSettings,piSettings,proof),tgSettings);
       
            if(proof == null){
                    bottomComponent = new JLabel("No proof has been loaded: those are the default settings.");
            }else{
                    bottomComponent = new JButton("Save as Default Values");
                    ((JButton)bottomComponent).addActionListener(new ActionListener() {
                        
                        @Override
                        public void actionPerformed(ActionEvent ev) {
                               settingsModel.storeAsDefault();
                                
                        }
                });
            }
            SettingsDialog dialog = new SettingsDialog(settingsModel,settingsModel.getStartComponent(),
                            new ActionListener() {
                
                @Override
                public void actionPerformed(ActionEvent event) {
                        switch(event.getID()){
                        case SettingsDialog.APPLY_BUTTON:
                                settingsModel.apply();
                                break;
                                
                        case SettingsDialog.CANCEL_BUTTON:
                                ((JDialog)event.getSource()).dispose();
                                break;
                                
                        case SettingsDialog.OKAY_BUTTON:
                                settingsModel.apply();
                                
                                ((JDialog)event.getSource()).dispose();
                               
                                break;
                        }
                               
                }
            },bottomComponent);
            dialog.setTitle("Settings for Decision Procedures");
            dialog.setLocationRelativeTo(null);
            dialog.setVisible(true);

    }

}
