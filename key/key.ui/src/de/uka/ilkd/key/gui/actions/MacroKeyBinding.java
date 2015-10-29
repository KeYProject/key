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

import javax.swing.AbstractAction;
import javax.swing.JComponent;
import javax.swing.KeyStroke;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.ProofMacroMenu;
import de.uka.ilkd.key.gui.ProofMacroWorker;
import de.uka.ilkd.key.gui.nodeviews.SequentView;
import de.uka.ilkd.key.gui.utilities.KeyStrokeManager;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.pp.PosInSequent;

/**
 * This class provides means to run macros with key bindings such that these can
 * be bound to the main window making them independent of any menu.
 *
 * @author Mattias Ulbrich
 */

@SuppressWarnings("serial")
public class MacroKeyBinding extends AbstractAction {

    private final SequentView sequentView;
    private final KeYMediator mediator;
    private final ProofMacro macro;

    public MacroKeyBinding(KeYMediator mediator, SequentView sequentView, ProofMacro macro) {
        super("Invoking macro " + macro.getClass());
        this.sequentView = sequentView;
        this.mediator = mediator;
        this.macro = macro;
    }

    @Override
    public void actionPerformed(ActionEvent e) {

        PosInSequent mousePos = sequentView.getLastPosInSequent();
        if(mousePos == null) {
            return;
        }

        PosInOccurrence posInOcc = mousePos.getPosInOccurrence();
        final ProofMacroWorker worker = new ProofMacroWorker(macro, mediator, posInOcc);
        mediator.stopInterface(true);
        mediator.setInteractive(false);
        mediator.addInterruptedListener(worker);
        worker.execute();
    }

    public static void registerMacroKeyBindings(KeYMediator mediator, SequentView sequentView, JComponent comp) {

        for (final ProofMacro macro : ProofMacroMenu.REGISTERED_MACROS) {
            KeyStroke ks = KeyStrokeManager.get(macro);
            if(ks != null) {
                String command = "invoke macro " + macro.getClass();
                comp.getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT).put(ks, command);
                comp.getActionMap().put(command, new MacroKeyBinding(mediator, sequentView, macro));
            }
        }
    }

}
