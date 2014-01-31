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

public class PrettyPrintToggleAction extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = 8633254204256247698L;

    public PrettyPrintToggleAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("Use pretty syntax");
	setTooltip("If ticked, infix notations are used.");
	final boolean prettySyntax = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUsePretty();
	NotationInfo.PRETTY_SYNTAX = prettySyntax;
	setSelected(prettySyntax);
	//setSelected(NotationInfo.PRETTY_SYNTAX);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean selected = ((JCheckBoxMenuItem) e.getSource()).isSelected();
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUsePretty(selected);
	NotationInfo.PRETTY_SYNTAX = selected;
	mainWindow.getUnicodeToggleAction().setEnabled(selected);
	mainWindow.getHidePackagePrefixToggleAction().setEnabled(selected);
	mainWindow.makePrettyView();
    }

}
