/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.ProverTaskListener;
import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.BlockExecutionPO;
import de.uka.ilkd.key.proof.init.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.rule.BlockContractBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.ui.UserInterface;


/**
 *
 * @author christoph
 */
public class StartAuxiliaryBlockComputationMacro extends AbstractProofMacro {

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
    public boolean canApplyTo(KeYMediator mediator,
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

        final Proof proof = goals.head().proof();
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
    public ProofMacroFinishedInfo applyTo(KeYMediator mediator,
                                          ImmutableList<Goal> goals,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) {
        ProofMacroFinishedInfo info = new ProofMacroFinishedInfo(this, goals);
        final Proof proof = goals.head().proof();
        if (goals.head().node().parent() == null) {
            return info;
        }
        final RuleApp app = goals.head().node().parent().getAppliedRuleApp();
        if (!(app instanceof BlockContractBuiltInRuleApp)) {
            return info;
        }

        final InitConfig initConfig = proof.getEnv().getInitConfigForEnvironment();

        final BlockContractBuiltInRuleApp blockRuleApp = (BlockContractBuiltInRuleApp) app;
        final BlockContract contract = blockRuleApp.getContract();
        final IFProofObligationVars ifVars = blockRuleApp.getInformationFlowProofObligationVars();

        final BlockExecutionPO blockExecPO =
                new BlockExecutionPO(initConfig, contract,
                                     ifVars.symbExecVars.labelHeapAtPreAsAnonHeapFunc(),
                                     goals.head(), blockRuleApp.getExecutionContext(),
                                     proof.getServices());
        final UserInterface ui = mediator.getUI();
        try {
            final Proof p;
            synchronized (blockExecPO) {
                p = ui.createProof(initConfig, blockExecPO);
            }
            p.unionIFSymbols(proof.getIFSymbols());
            // stop interface again, because it is activated by the proof
            // change through startProver; the ProofMacroWorker will activate
            // it again at the right time
            mediator.stopInterface(true);
            mediator.setInteractive(false);
            info = new ProofMacroFinishedInfo(this, p);
        } catch (ProofInputException exc) {
            ExceptionDialog.showDialog(MainWindow.getInstance(), exc);
        }
        return info;
    }
}