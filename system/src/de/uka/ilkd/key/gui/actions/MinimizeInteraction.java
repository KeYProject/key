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

public class MinimizeInteraction extends MainWindowAction {

	/**
	 *
	 */
	private static final long serialVersionUID = 3453843972242689758L;

	public MinimizeInteraction(MainWindow mainWindow) {
		super(mainWindow);
		setTooltip("If ticked and automated strategy (play button) is used, the prover tries to minimize user interaction, "+
		"e.g., if the prover can find instantiations by itself, it will not ask the user to provide them. ");
		setName("Minimize Interaction");
	}

	@Override
	public void actionPerformed(ActionEvent e) {
		boolean b = ((JCheckBoxMenuItem) e.getSource()).isSelected();
		getMediator().setMinimizeInteraction(b);
		ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setTacletFilter(b);
	}

}