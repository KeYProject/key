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

import javax.swing.JCheckBoxMenuItem;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;

public class ToggleConfirmExitAction extends MainWindowAction {

	/**
	 *
	 */
	private static final long serialVersionUID = 3453843972242689758L;

	public ToggleConfirmExitAction(MainWindow mainWindow) {
		super(mainWindow);
		setTooltip("Ask for extra confirmation when trying to exit the prover");
		setName("Confirm Exit");
                setSelected(ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().confirmExit());
	}

	@Override
	public void actionPerformed(ActionEvent e) {
		boolean b = ((JCheckBoxMenuItem) e.getSource()).isSelected();
		ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setConfirmExit(b);
	}

}