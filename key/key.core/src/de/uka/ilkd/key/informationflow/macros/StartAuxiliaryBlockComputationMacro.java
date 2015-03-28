/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.informationflow.macros;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.informationflow.po.BlockExecutionPO;
import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
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
import de.uka.ilkd.key.rule.BlockContractBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.BlockContract;


/**
 *
 * @author christoph
 */
public class StartAuxiliaryBlockComputationMacro extends AbstractProofMacro implements StartSideProofMacro {

    @Override
    public String getName() {
        return "Start auxiliary computation for self-composition proofs";
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
        if (goals == null || goals.head() == null
                || goals.head().node() == null
                || goals.head().node().parent() == null) {
            return false;
        }
        if (posInOcc == null
                || posInOcc.subTerm() == null) {
            return false;
        }

        final Services services = proof.getServices();

        final RuleApp app = goals.head().node().parent().getAppliedRuleApp();
        if (!(app instanceof BlockContractBuiltInRuleApp)) {
            return false;
        }
        final BlockContractBuiltInRuleApp blockRuleApp =
                (BlockContractBuiltInRuleApp) app;
        final BlockContract contract = blockRuleApp.getContract();
        final IFProofObligationVars ifVars =
                blockRuleApp.getInformationFlowProofObligationVars();
        if (ifVars == null) {
            return false;
        }

        final InfFlowPOSnippetFactory f =
                POSnippetFactory.getInfFlowFactory(contract,
                                                   ifVars.c1,
                                                   ifVars.c2,
                                                   blockRuleApp.getExecutionContext(),
                                                   services);
        final Term selfComposedExec =
                f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_BLOCK_WITH_PRE_RELATION);

        return posInOcc.subTerm().equalsModRenaming(selfComposedExec);
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic,
                                          Proof proof,
                                          ImmutableList<Goal> goals,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws Exception {
        final BlockContractBuiltInRuleApp blockRuleApp = 
                (BlockContractBuiltInRuleApp) goals.head().node().parent().getAppliedRuleApp();

        final InitConfig initConfig = proof.getEnv().getInitConfigForEnvironment();

        final BlockContract contract = blockRuleApp.getContract();
        final IFProofObligationVars ifVars = blockRuleApp.getInformationFlowProofObligationVars();

        final BlockExecutionPO blockExecPO =
                new BlockExecutionPO(initConfig, contract,
                                     ifVars.symbExecVars.labelHeapAtPreAsAnonHeapFunc(),
                                     goals.head(), blockRuleApp.getExecutionContext(),
                                     proof.getServices());
        
        final InfFlowProof p;
        synchronized (blockExecPO) {
            p = (InfFlowProof) uic.createProof(initConfig, blockExecPO);
        }
        p.unionIFSymbols(((InfFlowProof) proof).getIFSymbols());
        
        ProofMacroFinishedInfo info = new ProofMacroFinishedInfo(this, p);
        info.addInfo(PROOF_MACRO_FINISHED_INFO_KEY_ORIGINAL_PROOF, proof);
        return info;
    }
}