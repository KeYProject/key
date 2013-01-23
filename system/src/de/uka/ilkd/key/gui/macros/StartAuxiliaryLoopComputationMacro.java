package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.LoopInvExecutionPO;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.InfFlowContractPO.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.LoopInvariant;

public class StartAuxiliaryLoopComputationMacro implements ProofMacro {

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
    public boolean canApplyTo(KeYMediator mediator, PosInOccurrence posInOcc) {
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

        if (!(app instanceof LoopInvariantBuiltInRuleApp)) {
            return false;
        }
        LoopInvariantBuiltInRuleApp loopInvRuleApp =
                (LoopInvariantBuiltInRuleApp) app;
        LoopInvariant loopInv = loopInvRuleApp.getInvariant();

        IFProofObligationVars ifVars =
                loopInvRuleApp.getInformationFlowProofObligationVars();
        InfFlowPOSnippetFactory f =
                POSnippetFactory.getInfFlowFactory(loopInv,
                                                   ifVars.c1,
                                                   ifVars.c2, services);
        Term selfComposedExec =
                f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_LOOP_WITH_INV_RELATION);

        return posInOcc.subTerm().equalsModRenaming(selfComposedExec);
    }

    @Override
    public void applyTo(KeYMediator mediator, PosInOccurrence posInOcc) {
        Proof proof = mediator.getSelectedProof();
        Goal goal = mediator.getSelectedGoal();
        InitConfig initConfig = proof.env().getInitConfig();

        if (goal.node().parent() == null) {
            return;
        }
        RuleApp app = goal.node().parent().getAppliedRuleApp();
        if (!(app instanceof LoopInvariantBuiltInRuleApp)) {
            return;
        }
        LoopInvariantBuiltInRuleApp loopInvRuleApp =
                (LoopInvariantBuiltInRuleApp) app;
        LoopInvariant loopInv = loopInvRuleApp.getInvariant();
        IFProofObligationVars ifVars =
                loopInvRuleApp.getInformationFlowProofObligationVars();

        LoopInvExecutionPO loopInvExecPO =
                new LoopInvExecutionPO(initConfig, loopInv, ifVars.symbExecVars, goal);

        ProblemInitializer pi =
                new ProblemInitializer(mediator.getUI(), mediator.getProfile(),
                                       mediator.getServices(), true,
                                       mediator.getUI());
        try {
            pi.startProver(initConfig, loopInvExecPO, 0);
        } catch (ProofInputException exc) {
            ExceptionDialog.showDialog(MainWindow.getInstance(), exc);
        }
    }
}