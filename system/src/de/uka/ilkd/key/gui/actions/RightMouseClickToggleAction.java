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

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;

@SuppressWarnings("serial")
public class RightMouseClickToggleAction extends MainWindowAction {

    public RightMouseClickToggleAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Right click for macros");
        setTooltip("If ticked, a right click on the sequent opens the strategy macro context menu");
        setSelected(ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().isRightClickMacro());
//        setSelected(ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().isRightClickMacro());
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean sel = isSelected();
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setRightClickMacros(sel);
//        ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().setRightClickMacros(sel);
    }
}