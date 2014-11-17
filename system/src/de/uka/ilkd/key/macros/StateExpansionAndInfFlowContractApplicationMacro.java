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

package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InfFlowPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;

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
    public String getDescription() {
        return "Extract the self-composed states after the merge of the "
                + "symbolic execution goals which is included in the proof "
                + "obligation generation from information flow contracts " +
                "and apply all relevant information flow contracts.";
    }

    @Override
    protected ProofMacro[] createProofMacroArray() {
        return new ProofMacro[] {
                new SelfcompositionStateExpansionMacro(),
                new PropositionalExpansionWithSimplificationMacro(),
                new FullUseInformationFlowContractMacro()
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
    public boolean canApplyTo(KeYMediator mediator,
                              ImmutableList<Goal> goals,
                              PosInOccurrence posInOcc) {

        final Proof proof = mediator.getSelectedProof();
        if (proof == null) {
            return false;
        }
        final Services services = proof.getServices();
        if (services == null) {
            return false;
        }
        final ProofOblInput poForProof =
                services.getSpecificationRepository().getProofOblInput(proof);
        return (poForProof instanceof InfFlowPO) && super.canApplyTo(mediator, goals, posInOcc);
    }
}
