// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.informationflow.macros;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.informationflow.po.AbstractInfFlowPO;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.PrepareInfFlowContractPreBranchesMacro;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.SequentialProofMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofOblInput;

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
        return "Applies all applicable information flow contract rules and " +
                "prepares the information flow pre branches.";
    }

    @Override
    protected ProofMacro[] createProofMacroArray() {
        return new ProofMacro[] {
                new UseInformationFlowContractMacro(),
                new PrepareInfFlowContractPreBranchesMacro()
        };
    }

    /**
     * {@inheritDoc}
     *
     * <p>
     * This compound macro is applicable if and only if the first macro is applicable.
     * If there is no first macro, this is not applicable.
     */
    @Override
    public boolean canApplyTo(Proof proof,
                              ImmutableList<Goal> goals,
                              PosInOccurrence posInOcc) {
        if (proof == null) {
            return false;
        }
        final Services services = proof.getServices();
        if (services == null) {
            return false;
        }
        final ProofOblInput poForProof =
                services.getSpecificationRepository().getProofOblInput(proof);
        return (poForProof instanceof AbstractInfFlowPO) && super.canApplyTo(proof, goals, posInOcc);
    }
}
