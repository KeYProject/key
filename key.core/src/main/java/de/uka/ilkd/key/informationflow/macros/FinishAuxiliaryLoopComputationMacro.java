/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.macros;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.po.LoopInvExecutionPO;
import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.informationflow.rule.tacletbuilder.LoopInfFlowUnfoldTacletBuilder;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopSpecification;

import org.key_project.util.collection.ImmutableList;

public class FinishAuxiliaryLoopComputationMacro extends AbstractFinishAuxiliaryComputationMacro {

    @Override
    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals, PosInOccurrence posInOcc) {
        if (proof != null && proof.getServices() != null) {
            final ProofOblInput poForProof =
                proof.getServices().getSpecificationRepository().getProofOblInput(proof);

            if (poForProof instanceof LoopInvExecutionPO) {
                final Node parentOfInitiatingGoal =
                    ((LoopInvExecutionPO) poForProof).getInitiatingGoal().node().parent();
                return parentOfInitiatingGoal != null && parentOfInitiatingGoal
                        .getAppliedRuleApp() instanceof LoopInvariantBuiltInRuleApp;
            }
        }

        return false;
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, final Proof proof,
            ImmutableList<Goal> goals, PosInOccurrence posInOcc, ProverTaskListener listener) {
        final ProofOblInput poForProof =
            proof.getServices().getSpecificationRepository().getProofOblInput(proof);
        final LoopInvExecutionPO loopInvExecPO = (LoopInvExecutionPO) poForProof;

        final Goal initiatingGoal = loopInvExecPO.getInitiatingGoal();
        final InfFlowProof initiatingProof = (InfFlowProof) initiatingGoal.proof();
        final Services services = initiatingProof.getServices();

        final LoopInvariantBuiltInRuleApp loopInvRuleApp =
            (LoopInvariantBuiltInRuleApp) initiatingGoal.node().parent().getAppliedRuleApp();
        LoopSpecification loopInv = loopInvRuleApp.retrieveLoopInvariantFromSpecification(services);
        loopInv = loopInv != null ? loopInv : loopInvRuleApp.getSpec();
        IFProofObligationVars ifVars = loopInvRuleApp.getInformationFlowProofObligationVars();
        ifVars = ifVars.labelHeapAtPreAsAnonHeapFunc();

        mergeNamespaces(initiatingProof, proof);

        // create and register resulting taclets
        final Term result = calculateResultingTerm(proof, ifVars, initiatingGoal);
        final LoopInfFlowUnfoldTacletBuilder tacletBuilder =
            new LoopInfFlowUnfoldTacletBuilder(services);
        tacletBuilder.setLoopInv(loopInv);
        tacletBuilder.setExecutionContext(loopInvRuleApp.getExecutionContext());
        tacletBuilder.setInfFlowVars(ifVars);
        tacletBuilder.setReplacewith(result);
        tacletBuilder.setGuard(loopInvExecPO.getGuard());
        final Taclet rwTaclet = tacletBuilder.buildTaclet();
        initiatingProof.addLabeledTotalTerm(result);
        initiatingProof.addLabeledIFSymbol(rwTaclet);
        initiatingGoal.addTaclet(rwTaclet, SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
        addContractApplicationTaclets(initiatingGoal, proof);
        initiatingProof.unionIFSymbols(((InfFlowProof) proof).getIFSymbols());
        initiatingProof.getIFSymbols().useProofSymbols();

        final ProofMacroFinishedInfo info = new ProofMacroFinishedInfo(this, initiatingGoal);

        // close auxiliary computation proof
        initiatingProof.addSideProof((InfFlowProof) proof);
        proof.dispose();

        return info;
    }
}
