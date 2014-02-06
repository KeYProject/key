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

import javax.swing.JCheckBoxMenuItem;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.pp.NotationInfo;

public final class HidePackagePrefixToggleAction extends MainWindowAction {

    private static final long serialVersionUID = 3184733794964047845L;

    public HidePackagePrefixToggleAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("Hide Package Prefix");
	setTooltip("If ticked, class names are written without package prefixes.");
	final boolean hidePackage = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().hidePackagePrefix();
	NotationInfo.HIDE_PACKAGE_PREFIX = hidePackage;
	setSelected(hidePackage);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean selected = ((JCheckBoxMenuItem) e.getSource()).isSelected();
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHidePackagePrefix(selected);
	NotationInfo.HIDE_PACKAGE_PREFIX = selected;
	mainWindow.makePrettyView();
    }

}
