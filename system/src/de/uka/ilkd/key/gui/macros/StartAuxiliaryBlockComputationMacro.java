/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.BlockExecutionPO;
import de.uka.ilkd.key.proof.init.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.rule.BlockContractBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.BlockContract;
import javax.swing.KeyStroke;


/**
 *
 * @author christoph
 */
public class StartAuxiliaryBlockComputationMacro implements ExtendedProofMacro {

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
    public boolean finishAfterMacro() {
        return true;
    }

    @Override
    public boolean canApplyTo(KeYMediator mediator,
                              PosInOccurrence posInOcc) {
        if (mediator.getSelectedProof() == null) {
            return false;
        }
        Goal goal = mediator.getSelectedGoal();
        return canApplyTo(mediator, goal, posInOcc);
    }

    @Override
    public boolean canApplyTo(KeYMediator mediator,
                              Goal goal,
                              PosInOccurrence posInOcc) {
        if (goal == null || goal.node() == null || goal.node().parent() == null) {
            return false;
        }
        if (posInOcc == null
                || posInOcc.subTerm() == null) {
            return false;
        }

        Proof proof = goal.proof();
        Services services = proof.getServices();

        RuleApp app = goal.node().parent().getAppliedRuleApp();
        if (!(app instanceof BlockContractBuiltInRuleApp)) {
            return false;
        }
        BlockContractBuiltInRuleApp blockRuleApp =
                (BlockContractBuiltInRuleApp) app;
        BlockContract contract = blockRuleApp.getContract();
        IFProofObligationVars ifVars =
                blockRuleApp.getInformationFlowProofObligationVars();
        if (ifVars == null) {
            return false;
        }

        InfFlowPOSnippetFactory f =
                POSnippetFactory.getInfFlowFactory(contract,
                                                   ifVars.c1,
                                                   ifVars.c2,
                                                   blockRuleApp.getExecutionContext(),
                                                   services);
        Term selfComposedExec =
                f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_BLOCK_WITH_PRE_RELATION);

        return posInOcc.subTerm().equalsModRenaming(selfComposedExec);
    }


    @Override
    public void applyTo(KeYMediator mediator,
                        PosInOccurrence posInOcc,
                        ProverTaskListener listener) {
        Goal goal = mediator.getSelectedGoal();
        applyTo(mediator, goal, posInOcc, listener);
    }

    @Override
    public void applyTo(KeYMediator mediator,
                        Goal goal,
                        PosInOccurrence posInOcc,
                        ProverTaskListener listener) {
        if (goal.node().parent() == null) {
            return;
        }
        RuleApp app = goal.node().parent().getAppliedRuleApp();
        if (!(app instanceof BlockContractBuiltInRuleApp)) {
            return;
        }

        Proof proof = goal.proof();
        InitConfig initConfig = proof.env().getInitConfig();

        BlockContractBuiltInRuleApp blockRuleApp = (BlockContractBuiltInRuleApp) app;
        BlockContract contract = blockRuleApp.getContract();
        IFProofObligationVars ifVars = blockRuleApp.getInformationFlowProofObligationVars();

        BlockExecutionPO blockExecPO =
                new BlockExecutionPO(initConfig, contract,
                                     ifVars.symbExecVars.labelHeapAtPreAsAnonHeapFunc(),
                                     goal, blockRuleApp.getExecutionContext(),
                                     proof.getServices());
        ProblemInitializer pi =
                new ProblemInitializer(mediator.getUI(),
                                       mediator.getServices(), true,
                                       mediator.getUI());
        try {
            Proof p = pi.startProver(initConfig, blockExecPO, 0);
            p.unionIFSymbols(proof.getIFSymbols());
            // stop interface again, because it is activated by the proof
            // change through startProver; the ProofMacroWorker will activate
            // it again at the right time
            mediator.stopInterface(true);
            mediator.setInteractive(false);
        } catch (ProofInputException exc) {
            ExceptionDialog.showDialog(MainWindow.getInstance(), exc);
        }
    }


    @Override
    public KeyStroke getKeyStroke() {
        return null; // default implementation
    }
}