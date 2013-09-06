// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

import javax.swing.AbstractButton;
import javax.swing.Icon;
import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.util.MiscTools;

public class OneStepSimplificationToggleAction extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = -2772730241688097857L;

    public OneStepSimplificationToggleAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("One Step Simplification");
        putValue(MNEMONIC_KEY, KeyEvent.VK_O);
        putValue(ACCELERATOR_KEY, KeyStroke.getKeyStroke("control shift S"));
        putValue(SHORT_DESCRIPTION, "Toggle the aggregation of simplification rules." +
        		" Faster if on, more transparent if off.");
        
        Icon icon = IconFactory.oneStepSimplifier(MainWindow.TOOLBAR_ICON_SIZE);
        putValue(SMALL_ICON, icon);

        final boolean oneStepSimplificationOn = 
        		ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().oneStepSimplification();
//            ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().oneStepSimplification();
        setSelected(oneStepSimplificationOn);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
	boolean b = ((AbstractButton) e.getSource()).isSelected();
	ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setOneStepSimplification(b);
//	ProofSettings.DEFAULT_SETTINGS.getGeneralSettings()
//	        .setOneStepSimplification(b);
	OneStepSimplifier simplifier = MiscTools.findOneStepSimplifier(getMediator().getProfile());
	if (simplifier != null) {
	   simplifier.refresh(getMediator().getSelectedProof());
	}
    }

   @Override
   public boolean isEnabled() {
      return super.isEnabled() && getMediator().getProfile() instanceof JavaProfile;
   }
}