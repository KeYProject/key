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

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.GeneralSettings;

/**
 */
public final class GoalSelectAboveAction extends MainWindowAction {

    /**
     *
     */
    private static final long serialVersionUID = 4574670781882014092L;

    /**
     * Creates a new GoalBackAction.
     * @param mainWindow the main window this action belongs to
     * @param longName true iff long names (including the name of the rule to undo)
     * shall be displayed (e.g. in menu items)
     */
    public GoalSelectAboveAction(MainWindow mainWindow) {
        super(mainWindow);
        setAcceleratorLetter(KeyEvent.VK_K);
        setName("Select Goal Above");
        setTooltip("Changes selected goal in the proof-tree to the next item above the current one");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
            this.mainWindow.getProofTreeView().selectAbove();
    }
}
