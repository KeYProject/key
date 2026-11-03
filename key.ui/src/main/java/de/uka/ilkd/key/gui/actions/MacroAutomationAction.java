/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import javax.swing.Icon;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.useractions.ProofMacroUserAction;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.ui.MediatorProofControl;

import org.jspecify.annotations.NullMarked;

/**
 * Automation action that executes a proof macro.
 * <p>
 * This is a reusable wrapper for macro-based automation actions. Instead of creating separate
 * action classes for each macro, this generic wrapper can be used to expose any {@link ProofMacro}
 * as an automation option in the dropdown menu.
 * </p>
 *
 * @see ProofMacro
 */
@NullMarked
public class MacroAutomationAction extends AutoModeAction {

    private static final long serialVersionUID = 1L;

    /** The proof macro to execute when this action is triggered. */
    private final ProofMacro macro;

    /**
     * Creates a new macro automation action.
     *
     * @param mainWindow the main window this action belongs to
     * @param macro the proof macro to execute
     * @param icon the icon displayed on the action button
     */
    /**
     * The action-configuration setters are called on {@code this} while the receiver is still
     * under initialization (EISOP initialization check); safe here, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public MacroAutomationAction(MainWindow mainWindow, ProofMacro macro, Icon icon) {
        super(mainWindow, icon);
        this.macro = macro;
        setName(macro.getName());
        setTooltip(macro.getDescription() + " (shift-click = run on whole proof)");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        KeYMediator mediator = getMediator();
        MediatorProofControl proofControl = mediator.getUI().getProofControl();
        if (mediator.isInAutoMode()) {
            proofControl.stopAutoMode();
        } else {
            if ((e.getModifiers() & ActionEvent.SHIFT_MASK) != 0) {
                Proof proof = mediator.getSelectedProof();
                if (proof == null) {
                    throw new NullPointerException("No proof selected for whole-proof macro.");
                }
                new ProofMacroUserAction(mediator, macro, proof.root(), null).actionPerformed(e);
            } else {
                new ProofMacroUserAction(mediator, macro, null).actionPerformed(e);
            }
        }
    }

    @Override
    public String toString() {
        return (String) getValue(NAME);
    }
}
