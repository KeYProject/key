/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.macros;

import de.uka.ilkd.key.informationflow.po.AbstractInfFlowPO;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.PropositionalExpansionWithSimplificationMacro;
import de.uka.ilkd.key.macros.SequentialProofMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofOblInput;

import org.key_project.util.collection.ImmutableList;

/**
 *
 * @author christoph scheben
 */
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
    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals, PosInOccurrence posInOcc) {
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
                && super.canApplyTo(proof, goals, posInOcc);
    }
}
