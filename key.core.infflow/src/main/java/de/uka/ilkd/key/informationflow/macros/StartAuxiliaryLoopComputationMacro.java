/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.informationflow.macros;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.po.LoopInvExecutionPO;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.informationflow.rule.InfFlowLoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.macros.AbstractProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.speclang.LoopSpecification;

import org.key_project.prover.engine.ProverTaskListener;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;

@NullMarked
public class StartAuxiliaryLoopComputationMacro extends AbstractProofMacro
        implements StartSideProofMacro {

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
        return "In order to increase the efficiency of self-composition "
            + "proofs, this macro starts a side calculation which does "
            + "the symbolic execution only once. The result is "
            + "instantiated twice with the variable to be used in the "
            + "two executions of the self-composition.";
    }

    @Override
    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals,
            @Nullable PosInOccurrence posInOcc) {
        if (posInOcc == null || goals == null || goals.isEmpty()) {
            return false;
        }
        final Goal goal = goals.head();
        final Node parent = goal.node().parent();
        if (parent == null) {
            return false;
        }

        JTerm term = (JTerm) posInOcc.subTerm();
        if (term == null) {
            return false;
        }
        final Services services = proof.getServices();

        RuleApp app = parent.getAppliedRuleApp();
        if (!(app instanceof InfFlowLoopInvariantBuiltInRuleApp loopInvRuleApp)) {
            return false;
        }
        final LoopSpecification loopInv = loopInvRuleApp.getSpec();
        final IFProofObligationVars ifVars = loopInvRuleApp.getInformationFlowProofObligationVars();
        if (ifVars == null) {
            return false;
        }
        final ExecutionContext executionContext = loopInvRuleApp.getExecutionContext();
        final JTerm guardTerm = loopInvRuleApp.getGuard();

        final InfFlowPOSnippetFactory f = POSnippetFactory.getInfFlowFactory(loopInv, ifVars.c1,
            ifVars.c2, executionContext, guardTerm, services);
        final JTerm selfComposedExec =
            f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_LOOP_WITH_INV_RELATION);

        return RENAMING_TERM_PROPERTY.equalsModThisProperty(term, selfComposedExec);
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof,
            ImmutableList<Goal> goals, @Nullable PosInOccurrence posInOcc,
            @Nullable ProverTaskListener listener)
            throws Exception {
        final Node parent = goals.head().node().parent();
        if (parent == null) {
            throw new NullPointerException("No parent node of the goal.");
        }
        final RuleApp ruleApp = parent.getAppliedRuleApp();
        if (ruleApp == null) {
            throw new NullPointerException("No applied rule app on the parent node.");
        }
        final var loopInvRuleApp = (InfFlowLoopInvariantBuiltInRuleApp) ruleApp;

        final ProofEnvironment env = proof.getEnv();
        if (env == null) {
            throw new NullPointerException("No proof environment.");
        }
        final InitConfig initConfig = env.getInitConfigForEnvironment();

        final LoopSpecification loopInv = loopInvRuleApp.getSpec();
        final IFProofObligationVars ifVars = loopInvRuleApp.getInformationFlowProofObligationVars();
        if (ifVars == null) {
            throw new NullPointerException("No information flow proof obligation variables for "
                + "the rule application.");
        }
        final ExecutionContext executionContext = loopInvRuleApp.getExecutionContext();
        final JTerm guardTerm = loopInvRuleApp.getGuard();

        final LoopInvExecutionPO loopInvExecPO = new LoopInvExecutionPO(initConfig, loopInv,
            ifVars.symbExecVars.labelHeapAtPreAsAnonHeapFunc(), goals.head(), executionContext,
            guardTerm, proof.getServices());

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
