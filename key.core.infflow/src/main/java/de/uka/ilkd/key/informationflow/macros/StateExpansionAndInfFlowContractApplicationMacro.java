/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.informationflow.macros;

import de.uka.ilkd.key.informationflow.po.AbstractInfFlowPO;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.PropositionalExpansionWithSimplificationMacro;
import de.uka.ilkd.key.macros.SequentialProofMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofOblInput;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 *
 * @author christoph scheben
 */
@NullMarked
public class StateExpansionAndInfFlowContractApplicationMacro extends SequentialProofMacro {

    @Override
    public String getName() {
        return "Self-composition state expansion with inf flow contracts";
    }

    @Override
    public String getCategory() {
        return "Information Flow";
    }

    @Override
    public String getScriptCommandName() {
        return "inf-flow-state-expansion";
    }

    @Override
    public String getDescription() {
        return "Extract the self-composed states after the merge of the "
            + "symbolic execution goals which is included in the proof "
            + "obligation generation from information flow contracts "
            + "and apply all relevant information flow contracts.";
    }

    @Override
    protected ProofMacro[] createProofMacroArray() {
        return new ProofMacro[] { new SelfcompositionStateExpansionMacro(),
            new PropositionalExpansionWithSimplificationMacro(),
            new FullUseInformationFlowContractMacro() };
    }


    /**
     * {@inheritDoc}
     *
     * <p>
     * This compound macro is applicable if and only if the first macro is applicable. If there is
     * no first macro, this is not applicable.
     */
    @Override
    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals,
            @Nullable PosInOccurrence posInOcc) {
        if (proof == null) {
            return false;
        }
        final Services services = proof.getServices();
        if (services == null) {
            return false;
        }
        final ProofOblInput poForProof =
            services.getSpecificationRepository().getProofOblInput(proof);
        return (poForProof instanceof AbstractInfFlowPO)
                && canApplyToSuper(proof, goals, posInOcc);
    }


    /**
     * Deliberately forwards the position of the occurrence to the base
     * implementation even when it is {@code null}: at macro level the position
     * is not meaningful and the base implementations only consult the goals
     * and forward the position unchanged, never dereferencing it. Requiring a
     * non-null position here would change the historical applicability of this
     * macro; the base signature is not nullness-annotated and cannot be
     * widened from this module.
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    private boolean canApplyToSuper(Proof proof, ImmutableList<Goal> goals,
            @Nullable PosInOccurrence posInOcc) {
        return super.canApplyTo(proof, goals, posInOcc);
    }
}
