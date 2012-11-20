/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.InfFlowContractPO.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.SymbolicExecutionPO;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.rule.BlockContractBuiltInRuleApp;
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
        ContractPO poForProof =
                services.getSpecificationRepository().getPOForProof(proof);
        if (!(poForProof instanceof SymbolicExecutionPO)) {
            return false;
        }
        SymbolicExecutionPO po = (SymbolicExecutionPO) poForProof;

        Goal goal = po.getInitiatingGoal();
        RuleApp app = goal.node().getAppliedRuleApp();
        if (!(app instanceof BlockContractBuiltInRuleApp)) {
            return false;
        }
        BlockContractBuiltInRuleApp blockRuleApp =
                (BlockContractBuiltInRuleApp)app;
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
        Services services = proof.getServices();

        ContractPO poForProof =
                services.getSpecificationRepository().getPOForProof(proof);
        if (!(poForProof instanceof SymbolicExecutionPO)) {
            return;
        }
        SymbolicExecutionPO po = (SymbolicExecutionPO) poForProof;
        InitConfig initConfig = proof.env().getInitConfig();

        Goal initiatingGoal = po.getInitiatingGoal();
        RuleApp app = initiatingGoal.node().getAppliedRuleApp();
        if (!(app instanceof BlockContractBuiltInRuleApp)) {
            return;
        }
        BlockContractBuiltInRuleApp blockRuleApp =
                (BlockContractBuiltInRuleApp)app;
        BlockContract contract = blockRuleApp.getContract();
        IFProofObligationVars ifVars =
                blockRuleApp.getInformationFlowProofObligationVars();

        InformationFlowContract ifContract =
                new InformationFlowContractImpl(contract, services);
        SymbolicExecutionPO symbExecPO =
                new SymbolicExecutionPO(initConfig, ifContract,
                                        ifVars.symbExecVars, goal);

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
