/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.BlockExecutionPO;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.InfFlowContractPO.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.SymbolicExecutionPO;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.rule.BlockContractBuiltInRuleApp;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.speclang.InformationFlowContractImpl;


/**
 *
 * @author christoph
 */
public class StartAuxiliaryBlockComputationMacro implements ProofMacro {

    @Override
    public String getName() {
        return "Start auxiliray computation for self-composition proofs";
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
    public boolean canApplyTo(KeYMediator mediator,
                              PosInOccurrence posInOcc) {
        if (posInOcc == null || posInOcc.subTerm() == null) {
            return false;
        }
        Proof proof = mediator.getSelectedProof();
        Services services = proof.getServices();

        Goal goal = mediator.getSelectedGoal();
        if (goal.node().parent() == null) {
            return false;
        }
        RuleApp app = goal.node().parent().getAppliedRuleApp();
        if (!(app instanceof BlockContractBuiltInRuleApp)) {
            return false;
        }
        BlockContractBuiltInRuleApp blockRuleApp =
                (BlockContractBuiltInRuleApp) app;
        BlockContract contract = blockRuleApp.getContract();
        IFProofObligationVars ifVars =
                blockRuleApp.getInformationFlowProofObligationVars();

        InfFlowPOSnippetFactory f =
                POSnippetFactory.getInfFlowFactory(contract,
                                                   ifVars.c1,
                                                   ifVars.c2, services);
        Term selfComposedExec =
                f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_BLOCK_WITH_PRE_RELATION);

        return posInOcc.subTerm().equalsModRenaming(selfComposedExec);
    }


    @Override
    public void applyTo(KeYMediator mediator,
                        PosInOccurrence posInOcc) {
        Proof proof = mediator.getSelectedProof();
        Goal goal = mediator.getSelectedGoal();
        InitConfig initConfig = proof.env().getInitConfig();

        if (goal.node().parent() == null) {
            return;
        }
        RuleApp app = goal.node().parent().getAppliedRuleApp();
        if (!(app instanceof BlockContractBuiltInRuleApp)) {
            return;
        }
        BlockContractBuiltInRuleApp blockRuleApp =
                (BlockContractBuiltInRuleApp) app;
        BlockContract contract = blockRuleApp.getContract();
        IFProofObligationVars ifVars =
                blockRuleApp.getInformationFlowProofObligationVars();

        ContractPO poForProof =
                proof.getServices().getSpecificationRepository().getPOForProof(proof);
        if (!(poForProof instanceof AbstractOperationPO)) {
            return;
        }
        ImmutableSet<NoPosTacletApp> initialTaclets =
                ((SymbolicExecutionPO) poForProof).getInitialTaclets();


        BlockExecutionPO symbExecPO =
                new BlockExecutionPO(initConfig, contract, ifVars.symbExecVars,
                                     goal, initialTaclets);

        ProblemInitializer pi =
                new ProblemInitializer(mediator.getUI(), mediator.getProfile(),
                                       mediator.getServices(), true,
                                       mediator.getUI());
        try {
            pi.startProver(initConfig, symbExecPO, 0);
        } catch (ProofInputException exc) {
            ExceptionDialog.showDialog(MainWindow.getInstance(), exc);
        }
    }
}
