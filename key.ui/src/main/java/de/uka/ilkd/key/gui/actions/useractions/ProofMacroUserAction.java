/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions.useractions;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.Node;

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

    /// Root of the subtree to run the macro from. If null, it is run from the selected node.
    private final Node node;

    public ProofMacroUserAction(KeYMediator mediator, ProofMacro macro, PosInOccurrence pio) {
        super(mediator, mediator.getSelectedProof());
        this.macro = macro;
        this.pio = pio;
        this.node = mediator.getSelectedNode();
    }

    public ProofMacroUserAction(KeYMediator mediator, ProofMacro macro, Node node,
            PosInOccurrence pio) {
        super(mediator, mediator.getSelectedProof());
        this.macro = macro;
        this.pio = pio;
        this.node = node;
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
        if (node == null) {
            mediator.getUI().getProofControl().runMacro(mediator.getSelectedNode(), macro, pio);
        } else {
            mediator.getUI().getProofControl().runMacro(node, macro, pio);
        }
    }
}
