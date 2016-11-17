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
import java.awt.event.KeyEvent;
import java.util.EventObject;

import javax.swing.AbstractButton;
import javax.swing.Icon;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SettingsListener;

public class OneStepSimplificationToggleAction extends MainWindowAction {
    public static final String NAME = "One Step Simplification";

    /**
     * 
     */
    private static final long serialVersionUID = -2772730241688097857L;
    
    /**
     * Listens for changes on {@code ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()}.
     * <p>
     * Such changes can occur in the Eclipse context when settings are changed in for instance the KeYIDE.
     */
    private final SettingsListener generalSettingsListener = new SettingsListener() {
       @Override
       public void settingsChanged(EventObject e) {
          handleGeneralSettingsChanged(e);
       }
    };

    public OneStepSimplificationToggleAction(MainWindow mainWindow) {
        super(mainWindow);
        setName(NAME);
        putValue(MNEMONIC_KEY, KeyEvent.VK_O);
        putValue(SHORT_DESCRIPTION, "Toggle the aggregation of simplification rules." 
                                    + " Faster if on, more transparent if off.");
        
        Icon icon = IconFactory.oneStepSimplifier(MainWindow.TOOLBAR_ICON_SIZE);
        putValue(SMALL_ICON, icon);

        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().addSettingsListener(generalSettingsListener); // Attention: The listener is never removed, because there is only one MainWindow!
    }
    
    protected void updateSelectedState() {
       final boolean oneStepSimplificationOn = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().oneStepSimplification();
       setSelected(oneStepSimplificationOn);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
	boolean b = ((AbstractButton) e.getSource()).isSelected();
	ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setOneStepSimplification(b);
   updateMainWindow();
    }
    
    protected void updateMainWindow() {
       OneStepSimplifier.refreshOSS(getMediator().getSelectedProof());
    }

    protected void handleGeneralSettingsChanged(EventObject e) {
       updateSelectedState();
       updateMainWindow();
    }

   @Override
   public boolean isEnabled() {
      return super.isEnabled() && getMediator().getProfile() instanceof JavaProfile;
   }
}