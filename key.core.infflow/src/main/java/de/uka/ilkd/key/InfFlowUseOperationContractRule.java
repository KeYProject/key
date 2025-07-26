/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key;

import de.uka.ilkd.key.informationflow.ProofObligationVars;
import de.uka.ilkd.key.informationflow.proof.InfFlowCheckInfo;
import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.informationflow.proof.init.StateVars;
import de.uka.ilkd.key.informationflow.rule.tacletbuilder.InfFlowMethodContractTacletBuilder;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;

/**
 * @author Alexander Weigl
 * @version 1 (8/3/25)
 */
@NullMarked
public class InfFlowUseOperationContractRule extends UseOperationContractRule {
    public static InfFlowUseOperationContractRule INSTANCE = new InfFlowUseOperationContractRule();

    protected InfFlowUseOperationContractRule() {
    }

    @Override
    public @NonNull ImmutableList<Goal> apply(Goal goal, RuleApp ruleApp) {
        return new InfFlowUseOperationContractRuleApplier(goal, ruleApp).apply();
    }

    protected static class InfFlowUseOperationContractRuleApplier
            extends UseOperationContractRuleApplier {
        protected InfFlowUseOperationContractRuleApplier(Goal goal, RuleApp ruleApp) {
            super(goal, ruleApp);
        }

        @Override
        protected JTerm getFinalPreTerm() {
            // termination has already been shown in the functional proof,
            // thus we do not need to show it again in information flow proofs.
            return tb.applySequential(new JTerm[] { inst.u(), atPreUpdates },
                tb.and(new JTerm[] { pre, reachableState }));
        }

        private void applyInfFlow(Goal goal) {
            if (!InfFlowCheckInfo.isInfFlow(goal)) {
                return;
            }

            var exception = tb.var(excVar);

            // prepare information flow analysis
            assert anonUpdateDatas.size() == 1
                    : "information flow extension " + "is at the moment not "
                        + "compatible with the " + "non-base-heap setting";
            AnonUpdateData anonUpdateData = anonUpdateDatas.head();

            final JTerm heapAtPre = anonUpdateData.methodHeapAtPre();
            final JTerm heapAtPost = anonUpdateData.methodHeap();

            // generate proof obligation variables
            final boolean hasSelf = contractSelf != null;
            final boolean hasRes = contractResult != null;
            final boolean hasExc = exception != null;

            final StateVars preVars = new StateVars(hasSelf ? contractSelf : null, contractParams,
                hasRes ? contractResult : null, hasExc ? exception : null, heapAtPre, mby);
            final StateVars postVars = new StateVars(hasSelf ? contractSelf : null, contractParams,
                hasRes ? contractResult : null, hasExc ? exception : null, heapAtPost, mby);
            final ProofObligationVars poVars = new ProofObligationVars(preVars, postVars, services);

            // generate information flow contract application predicate
            // and associated taclet
            InfFlowMethodContractTacletBuilder ifContractBuilder =
                new InfFlowMethodContractTacletBuilder(services);
            ifContractBuilder.setContract(contract);
            ifContractBuilder.setContextUpdate(atPreUpdates, inst.u());
            ifContractBuilder.setProofObligationVars(poVars);

            JTerm contractApplPredTerm = ifContractBuilder.buildContractApplPredTerm();
            Taclet informationFlowContractApp = ifContractBuilder.buildTaclet(goal);

            // add term and taclet to post goal
            goal.addFormula(new SequentFormula(contractApplPredTerm), true, false);
            goal.addTaclet(informationFlowContractApp, SVInstantiations.EMPTY_SVINSTANTIATIONS,
                true);

            // information flow proofs might get easier if we add the (proved)
            // method contract precondition as an assumption to the post goal
            // (in case the precondition cannot be proved easily)
            goal.addFormula(new SequentFormula(finalPreTerm), true, false);
            final InfFlowProof proof = (InfFlowProof) goal.proof();
            proof.addIFSymbol(contractApplPredTerm);
            proof.addIFSymbol(informationFlowContractApp);
            proof.addGoalTemplates(informationFlowContractApp);
        }


        @Override
        protected void createPostGoal(Goal postGoal) {
            super.createPostGoal(postGoal);
            applyInfFlow(postGoal);
        }
    }
}
