/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.informationflow.macros;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.po.InfFlowContractPO;
import de.uka.ilkd.key.informationflow.po.SymbolicExecutionPO;
import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.informationflow.rule.tacletbuilder.MethodInfFlowUnfoldTacletBuilder;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.InformationFlowContract;

/**
 *
 * @author christoph
 */
public class FinishAuxiliaryMethodComputationMacro
        extends AbstractFinishAuxiliaryComputationMacro {

    @Override
    public boolean canApplyTo(Proof proof,
                              ImmutableList<Goal> goals,
                              PosInOccurrence posInOcc) {
        if (proof != null && proof.getServices() != null) {
            final ProofOblInput poForProof =
                proof.getServices().getSpecificationRepository().getProofOblInput(proof);
            if (poForProof instanceof SymbolicExecutionPO) {
                return true;
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

        final ProofOblInput poForProof =
                proof.getServices().getSpecificationRepository().getProofOblInput(proof);
        final Goal initiatingGoal = ((SymbolicExecutionPO) poForProof).getInitiatingGoal();
        final InfFlowProof initiatingProof = (InfFlowProof) initiatingGoal.proof();
        final Services services = initiatingProof.getServices();
        final InfFlowContractPO ifPO =
                (InfFlowContractPO) services.getSpecificationRepository()
                                         .getProofOblInput(initiatingProof);
        final IFProofObligationVars ifVars = ifPO.getIFVars().labelHeapAtPreAsAnonHeapFunc();
        final InformationFlowContract ifContract = ifPO.getContract();

        // create and register resulting taclets
        final Term result = calculateResultingTerm(proof, ifVars, initiatingGoal);
        final MethodInfFlowUnfoldTacletBuilder tacletBuilder =
                new MethodInfFlowUnfoldTacletBuilder(services);
        tacletBuilder.setContract(ifContract);
        tacletBuilder.setInfFlowVars(ifVars);
        tacletBuilder.setReplacewith(result);
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