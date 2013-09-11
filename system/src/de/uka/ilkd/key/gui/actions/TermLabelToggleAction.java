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

/*
 * Toggle term labels with this MainWindowAction. If turned off,
 * no term labels are displayed in SequentView.
 */
public class TermLabelToggleAction extends MainWindowAction {

    public TermLabelToggleAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Hide term labels");
        setTooltip("Turn off term labels, if not needed.");
        setSelected(NotationInfo.TERMLABELS_HIDDEN);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean selected = ((JCheckBoxMenuItem) e.getSource()).isSelected();
        NotationInfo.TERMLABELS_HIDDEN = selected;
        mainWindow.makePrettyView();
    }

}
