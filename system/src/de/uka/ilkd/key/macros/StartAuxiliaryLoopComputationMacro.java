package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.LoopInvExecutionPO;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.LoopInvariant;
import javax.swing.KeyStroke;

public class StartAuxiliaryLoopComputationMacro extends AbstractProofMacro {

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
        Proof proof = goals.head().proof();
        Services services = proof.getServices();

        RuleApp app = goals.head().node().parent().getAppliedRuleApp();
        if (!(app instanceof LoopInvariantBuiltInRuleApp)) {
            return false;
        }
        final LoopInvariantBuiltInRuleApp loopInvRuleApp =
                (LoopInvariantBuiltInRuleApp) app;
        final LoopInvariant loopInv = loopInvRuleApp.getInvariant();
        final IFProofObligationVars ifVars =
                loopInvRuleApp.getInformationFlowProofObligationVars();
        if (ifVars == null) {
            return false;
        }
        final ExecutionContext executionContext =
                loopInvRuleApp.getExecutionContext();
        final Term guardTerm = loopInvRuleApp.getGuard();

        InfFlowPOSnippetFactory f =
                POSnippetFactory.getInfFlowFactory(loopInv, ifVars.c1,
                                                   ifVars.c2, executionContext,
                                                   guardTerm, services);
        Term selfComposedExec =
                f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_LOOP_WITH_INV_RELATION);

        return posInOcc.subTerm().equalsModRenaming(selfComposedExec);
    }

    @Override
    public ProofMacroFinishedInfo applyTo(KeYMediator mediator,
                                          ImmutableList<Goal> goals,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) {
        ProofMacroFinishedInfo info = new ProofMacroFinishedInfo(this, goals);
        if (goals.head().node().parent() == null) {
            return info;
        }
        final Proof proof = goals.head().proof();
        RuleApp app = goals.head().node().parent().getAppliedRuleApp();
        if (!(app instanceof LoopInvariantBuiltInRuleApp)) {
            return info;
        }

        InitConfig initConfig = proof.env().getInitConfig();

        final LoopInvariantBuiltInRuleApp loopInvRuleApp =
                (LoopInvariantBuiltInRuleApp) app;
        final LoopInvariant loopInv = loopInvRuleApp.getInvariant();
        final IFProofObligationVars ifVars =
                loopInvRuleApp.getInformationFlowProofObligationVars();
        final ExecutionContext executionContext =
                loopInvRuleApp.getExecutionContext();
        final Term guardTerm = loopInvRuleApp.getGuard();


        LoopInvExecutionPO loopInvExecPO =
                new LoopInvExecutionPO(initConfig, loopInv,
                                       ifVars.symbExecVars.labelHeapAtPreAsAnonHeapFunc(),
                                       goals.head(), executionContext,
                                       guardTerm,
                                       proof.getServices());
        ProblemInitializer pi =
                new ProblemInitializer(mediator.getUI(),
                                       mediator.getServices(),
                                       mediator.getUI());
        try {
            Proof p = pi.startProver(initConfig, loopInvExecPO, 0);
            p.unionIFSymbols(proof.getIFSymbols());
            // stop interface again, because it is activated by the proof
            // change through startProver; the ProofMacroWorker will activate
            // it again at the right time
            mediator.stopInterface(true);
            mediator.setInteractive(false);
            info = new ProofMacroFinishedInfo(this, p.openEnabledGoals(), p);
        } catch (ProofInputException exc) {
            ExceptionDialog.showDialog(MainWindow.getInstance(), exc);
        }
        return info;
    }


    @Override
    public KeyStroke getKeyStroke() {
        return null; // default implementation
    }
}