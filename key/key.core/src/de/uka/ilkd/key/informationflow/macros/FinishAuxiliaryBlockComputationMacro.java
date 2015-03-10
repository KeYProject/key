/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.informationflow.macros;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.informationflow.po.BlockExecutionPO;
import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.informationflow.rule.tacletbuilder.BlockInfFlowUnfoldTacletBuilder;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.BlockContractBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.BlockContract;

/**
 *
 * @author christoph
 */
public class FinishAuxiliaryBlockComputationMacro
        extends AbstractFinishAuxiliaryComputationMacro {

    @Override
    public boolean canApplyTo(Proof proof,
                              ImmutableList<Goal> goals,
                              PosInOccurrence posInOcc) {        
        if (proof != null && proof.getServices() != null) {
            final ProofOblInput poForProof =
                    proof.getServices().getSpecificationRepository().getProofOblInput(proof);
            if (poForProof instanceof BlockExecutionPO) {
                final Goal initiatingGoal = ((BlockExecutionPO)poForProof).getInitiatingGoal();
                if (initiatingGoal.node().parent() != null) {
                    final RuleApp app = initiatingGoal.node().parent().getAppliedRuleApp();
                    if (app instanceof BlockContractBuiltInRuleApp) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic,
                                          final Proof proof,
                                          ImmutableList<Goal> goals,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) {
        assert canApplyTo(proof, goals, posInOcc);

        final ProofOblInput poForProof =
                proof.getServices().getSpecificationRepository().getProofOblInput(proof);
        
        // must be BlockExecutionPO otherwise canApplyTo would not have been true
        // and we assume that before calling this method, the applicability of the macro was checked
        
        final Goal initiatingGoal = ((BlockExecutionPO) poForProof).getInitiatingGoal();
        final InfFlowProof initiatingProof = (InfFlowProof) initiatingGoal.proof();
        final Services services = initiatingProof.getServices();

        // initiating goal must not be root and it is the result of a block contract application
        // otherwise the applicable check would have already failed
        // and we assume that before calling this method, the applicability of the macro was checked
        final RuleApp app = initiatingGoal.node().parent().getAppliedRuleApp();

        final BlockContractBuiltInRuleApp blockRuleApp = (BlockContractBuiltInRuleApp)app;
        final BlockContract contract = blockRuleApp.getContract();
        IFProofObligationVars ifVars = blockRuleApp.getInformationFlowProofObligationVars();
        ifVars = ifVars.labelHeapAtPreAsAnonHeapFunc();

        // create and register resulting taclets
        final Term result = calculateResultingTerm(proof, ifVars, initiatingGoal);
        final Taclet rwTaclet = buildBlockInfFlowUnfoldTaclet(
                services, blockRuleApp, contract, ifVars, result);
        
        initiatingProof.addLabeledTotalTerm(result);
        initiatingProof.addLabeledIFSymbol(rwTaclet);
        initiatingGoal.addTaclet(rwTaclet, SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
        
        addContractApplicationTaclets(initiatingGoal, proof);
        initiatingProof.unionIFSymbols(((InfFlowProof)proof).getIFSymbols());
        initiatingProof.getIFSymbols().useProofSymbols();

        // close auxiliary computation proof
        initiatingProof.addSideProof((InfFlowProof) proof);
        proof.dispose();
        
        return new ProofMacroFinishedInfo(this, initiatingGoal);
    }

    /**
     * constructs a taclet to unfold block contracts for information flow reasoning
     * @param services the Services
     * @param blockRuleApp the rule application of the block contract
     * @param contract the block contract
     * @param ifVars variables specific for the IF proof obligation
     * @param result the term representing the result (?) // TODO: someone who knows what the taclet does please provide a description
     * @return the created taclet
     */
    private Taclet buildBlockInfFlowUnfoldTaclet(
            final Services services,
            final BlockContractBuiltInRuleApp blockRuleApp,
            final BlockContract contract, IFProofObligationVars ifVars,
            final Term result) {
        final BlockInfFlowUnfoldTacletBuilder tacletBuilder =
                new BlockInfFlowUnfoldTacletBuilder(services);
        tacletBuilder.setContract(contract);
        tacletBuilder.setExecutionContext(blockRuleApp.getExecutionContext());
        tacletBuilder.setInfFlowVars(ifVars);
        tacletBuilder.setReplacewith(result);
        return tacletBuilder.buildTaclet();
    }
}