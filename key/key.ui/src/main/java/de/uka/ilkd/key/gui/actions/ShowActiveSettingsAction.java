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

import javax.swing.JDialog;
import javax.swing.JLabel;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.smt.SettingsDialog;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ProofSettings;

/**
 * for debugging - opens a window with the settings from current Proof and the
 * default settings
 */
public class ShowActiveSettingsAction extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = -3038735283059371442L;

    public ShowActiveSettingsAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("Show All Active Settings");
        setIcon(IconFactory.properties(16));
    }

    @Override
    public void actionPerformed(ActionEvent e) {

	
	
	ProofSettings settings = (getMediator().getSelectedProof() == null) ?
			                               ProofSettings.DEFAULT_SETTINGS :
				                           getMediator().getSelectedProof().getSettings(); 
	
	SettingsTreeModel model = new SettingsTreeModel(settings, ProofIndependentSettings.DEFAULT_INSTANCE);
	
	SettingsDialog dialog = new SettingsDialog(model, model.getStartComponent(), new ActionListener() {
        
        @Override
        public void actionPerformed(ActionEvent event) {
                switch(event.getID()){
                case SettingsDialog.APPLY_BUTTON:
                	
                        break;
                        
                case SettingsDialog.CANCEL_BUTTON:
                        ((JDialog)event.getSource()).dispose();
                        break;
                        
                case SettingsDialog.OKAY_BUTTON:
                        
                        
                        ((JDialog)event.getSource()).dispose();
                       
                        break;
                }
                       
        }
    }, new JLabel(""),false);
	dialog.setTitle("All Active Settings");
    dialog.setLocationRelativeTo(null);
    dialog.setVisible(true);
    }
    

}