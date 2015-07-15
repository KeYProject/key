/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.informationflow.macros;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.informationflow.po.InfFlowContractPO;
import de.uka.ilkd.key.informationflow.po.SymbolicExecutionPO;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.macros.AbstractProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;

/**
 *
 * @author christoph
 */
public class StartAuxiliaryMethodComputationMacro extends AbstractProofMacro implements StartSideProofMacro {

    @Override
    public String getName() {
        return "Start auxiliary computation for self-composition proofs";
    }

    @Override
    public String getCategory() {
        return "Information Flow";
    }

    @Override
    public String getDescription() {
        return "In order to increase the efficiency of self-composition " +
               "proofs, this macro starts a side calculation which does " +
               "the symbolic execution only once. The result is " +
               "instantiated twice with the variable to be used in the " +
               "two executions of the self-composition.";
    }

    @Override
    public boolean canApplyTo(Proof proof,
                              ImmutableList<Goal> goals,
                              PosInOccurrence posInOcc) {
        if (goals == null || goals.head() == null) {
            return false;
        }
        if (posInOcc == null
                || posInOcc.subTerm() == null) {
            return false;
        }
        Services services = proof.getServices();
        ProofOblInput poForProof =
                services.getSpecificationRepository().getProofOblInput(proof);
        if (!(poForProof instanceof InfFlowContractPO)) {
            return false;
        }
        final InfFlowContractPO po = (InfFlowContractPO) poForProof;

        final InfFlowPOSnippetFactory f =
                POSnippetFactory.getInfFlowFactory(po.getContract(),
                                                   po.getIFVars().c1,
                                                   po.getIFVars().c2, services);
        final Term selfComposedExec =
                f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_EXECUTION_WITH_PRE_RELATION);

        return posInOcc.subTerm().equalsModRenaming(selfComposedExec);
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic,
                                          Proof proof,
                                          ImmutableList<Goal> goals,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws Exception {
        final Services services = proof.getServices();
        final InfFlowContractPO po = (InfFlowContractPO) services.getSpecificationRepository().getProofOblInput(proof);

        final InitConfig initConfig = proof.getEnv().getInitConfigForEnvironment();

        final SymbolicExecutionPO symbExecPO =
                new SymbolicExecutionPO(initConfig, po.getContract(),
                                        po.getIFVars().symbExecVars.labelHeapAtPreAsAnonHeapFunc(),
                                        goals.head(), proof.getServices());
        
        final InfFlowProof p;
        synchronized (symbExecPO) {
            p = (InfFlowProof) uic.createProof(initConfig, symbExecPO);
        }
        p.unionIFSymbols(((InfFlowProof) proof).getIFSymbols());
        
        ProofMacroFinishedInfo info = new ProofMacroFinishedInfo(this, p);
        info.addInfo(PROOF_MACRO_FINISHED_INFO_KEY_ORIGINAL_PROOF, proof);
        return info;
    }
}