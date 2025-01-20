/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import javax.swing.AbstractAction;
import javax.swing.JComponent;
import javax.swing.KeyStroke;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.ProofMacroMenu;
import de.uka.ilkd.key.gui.actions.useractions.ProofMacroUserAction;
import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager;
import de.uka.ilkd.key.gui.nodeviews.SequentView;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.pp.PosInSequent;

/**
 * This class provides means to run macros with key bindings such that these can be bound to the
 * main window making them independent of any menu.
 *
 * @author Mattias Ulbrich
 */
public class MacroKeyBinding extends AbstractAction {
    private static final long serialVersionUID = 1529344940571000989L;

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

        PosInOccurrence posInOcc = null;
        boolean isGoal = mediator.getSelectedGoal() != null;

        if (isGoal) {
            PosInSequent mousePos = sequentView.getLastPosInSequent();
            if (mousePos != null) {
                posInOcc = mousePos.getPosInOccurrence();
            }
        }

        if (macro.canApplyTo(mediator.getSelectedNode(), posInOcc)) {
            new ProofMacroUserAction(mediator, macro, posInOcc, mediator.getSelectedProof())
                    .actionPerformed(e);
        }
    }

    /**
     * Register the key bindings for all macros that are already configured in the
     * {@link KeyStrokeManager}.
     *
     * @param mediator KeY mediator
     * @param sequentView sequent view
     * @param comp component to register key bindings in
     */
    public static void registerMacroKeyBindings(KeYMediator mediator, SequentView sequentView,
            JComponent comp) {

        for (final ProofMacro macro : ProofMacroMenu.REGISTERED_MACROS) {
            KeyStroke ks = KeyStrokeManager.get(macro);
            if (ks != null) {
                String command = "invoke macro " + macro.getClass();
                comp.getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT).put(ks, command);
                comp.getActionMap().put(command, new MacroKeyBinding(mediator, sequentView, macro));
            }
        }
    }

}
