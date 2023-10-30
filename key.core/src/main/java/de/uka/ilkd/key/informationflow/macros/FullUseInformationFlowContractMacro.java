/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.macros;

import de.uka.ilkd.key.informationflow.po.AbstractInfFlowPO;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.PrepareInfFlowContractPreBranchesMacro;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.SequentialProofMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofOblInput;

import org.key_project.util.collection.ImmutableList;

/**
 *
 * @author christoph scheben
 */
public class FullUseInformationFlowContractMacro extends SequentialProofMacro {

    @Override
    public String getName() {
        return "Use information flow contracts";
    }

    @Override
    public String getCategory() {
        return "Information Flow";
    }

    @Override
    public String getDescription() {
        return "Applies all applicable information flow contract rules and "
            + "prepares the information flow pre branches.";
    }

    @Override
    public String getScriptCommandName() {
        return "use-inf-flow-contracts";
    }

    @Override
    protected ProofMacro[] createProofMacroArray() {
        return new ProofMacro[] { new UseInformationFlowContractMacro(),
            new PrepareInfFlowContractPreBranchesMacro() };
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
