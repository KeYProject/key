package de.uka.ilkd.key.informationflow.macros;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.po.LoopInvExecutionPO;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.macros.AbstractProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.LoopInvariant;

public class StartAuxiliaryLoopComputationMacro extends AbstractProofMacro implements StartSideProofMacro {

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

        final InfFlowPOSnippetFactory f =
                POSnippetFactory.getInfFlowFactory(loopInv, ifVars.c1,
                                                   ifVars.c2, executionContext,
                                                   guardTerm, services);
        final Term selfComposedExec =
                f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_LOOP_WITH_INV_RELATION);

        return posInOcc.subTerm().equalsModRenaming(selfComposedExec);
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic,
                                          Proof proof,
                                          ImmutableList<Goal> goals,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws Exception {
        final LoopInvariantBuiltInRuleApp loopInvRuleApp = (LoopInvariantBuiltInRuleApp) 
                goals.head().node().parent().getAppliedRuleApp();

        final InitConfig initConfig = proof.getEnv().getInitConfigForEnvironment();

        final LoopInvariant loopInv = loopInvRuleApp.getInvariant();
        final IFProofObligationVars ifVars =
                loopInvRuleApp.getInformationFlowProofObligationVars();
        final ExecutionContext executionContext =
                loopInvRuleApp.getExecutionContext();
        final Term guardTerm = loopInvRuleApp.getGuard();

        final LoopInvExecutionPO loopInvExecPO =
                new LoopInvExecutionPO(initConfig, loopInv,
                                       ifVars.symbExecVars.labelHeapAtPreAsAnonHeapFunc(),
                                       goals.head(), executionContext,
                                       guardTerm,
                                       proof.getServices());
        
        final InfFlowProof p;
        synchronized (loopInvExecPO) {
            p = (InfFlowProof) uic.createProof(initConfig, loopInvExecPO);
        }
        p.unionIFSymbols(((InfFlowProof) proof).getIFSymbols());
       
        ProofMacroFinishedInfo info = new ProofMacroFinishedInfo(this, p);
        info.addInfo(PROOF_MACRO_FINISHED_INFO_KEY_ORIGINAL_PROOF, proof);
        return info;
    }
}