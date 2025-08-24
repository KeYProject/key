/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions.useractions;

import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.prover.sequent.PosInOccurrence;

/**
 * User action to apply a proof macro.
 *
 * @author Arne Keller
 */
public class ProofMacroUserAction extends ProofModifyingUserAction {
    /**
     * The macro to execute in this action.
     */
    private final ProofMacro macro;
    /**
     * The position to apply the macro on.
     */
    private final PosInOccurrence pio;

    public ProofMacroUserAction(KeYMediator mediator, ProofMacro macro, PosInOccurrence pio,
            Proof proof) {
        super(mediator, proof);
        this.macro = macro;
        this.pio = pio;

        setTooltip(macro.getDescription());
        final KeyStroke macroKey = KeyStrokeManager.get(macro);
        if (macroKey != null && pio == null) { // currently only for global macro applications
            setAcceleratorKey(macroKey);
        }
    }

    @Override
    public String name() {
        return "Macro: " + macro.getName();
    }

    @Override
    protected void apply() {
        if (mediator.isInAutoMode()) {
            return;
        }
        mediator.getUI().getProofControl().runMacro(mediator.getSelectedNode(), macro, pio);
    }
}
