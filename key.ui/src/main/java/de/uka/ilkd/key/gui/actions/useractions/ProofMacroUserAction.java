/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.actions.useractions;

import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.prover.sequent.PosInOccurrence;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * User action to apply a proof macro.
 *
 * @author Arne Keller
 */
@NullMarked
public class ProofMacroUserAction extends ProofModifyingUserAction {
    /**
     * The macro to execute in this action.
     */
    private final ProofMacro macro;
    /**
     * The position to apply the macro on.
     */
    private final @Nullable PosInOccurrence pio;

    /// Root of the subtree to run the macro from. If null, it is run from the selected node.
    private final @Nullable Node node;

    /**
     * Returns the currently selected proof, failing with an {@link NullPointerException} if no
     * proof is loaded. User actions are only ever created while a proof is selected; a missing
     * proof here is an inconsistent state in which the previous code crashed with an NPE during
     * the {@code super} call.
     */
    private static Proof requireSelectedProof(KeYMediator mediator) {
        Proof selectedProof = mediator.getSelectedProof();
        if (selectedProof == null) {
            throw new NullPointerException("No proof selected.");
        }
        return selectedProof;
    }

    public ProofMacroUserAction(KeYMediator mediator, ProofMacro macro,
            @Nullable PosInOccurrence pio) {
        super(mediator, requireSelectedProof(mediator));
        this.macro = macro;
        this.pio = pio;
        this.node = mediator.getSelectedNode();
    }

    public ProofMacroUserAction(KeYMediator mediator, ProofMacro macro, @Nullable Node node,
            @Nullable PosInOccurrence pio) {
        super(mediator, requireSelectedProof(mediator));
        this.macro = macro;
        this.pio = pio;
        this.node = node;
    }

    @Override
    public String name() {
        return "Macro: " + macro.getName();
    }

    /**
     * The macro position may legitimately be {@code null}: {@link ProofMacro#applyTo} declares a
     * {@code @Nullable PosInOccurrence} and global macros run without a position, yet the
     * proof-control interface parameter is annotated {@code @NonNull}, suppressed with a scoped
     * key.
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    @Override
    protected void apply() {
        if (mediator.isInAutoMode()) {
            return;
        }
        Node targetNode = node;
        if (targetNode == null) {
            targetNode = mediator.getSelectedNode();
        }
        if (targetNode == null) {
            // A macro cannot run without a node; in the previous code the macro worker crashed
            // with an NPE on {@code node.proof()} in this impossible no-selection state.
            throw new NullPointerException("No node selected to apply the macro.");
        }
        ProofControl proofControl = mediator.getUI().getProofControl();
        proofControl.runMacro(targetNode, macro, pio);
    }
}
