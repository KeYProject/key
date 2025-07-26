/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.wd;

import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.macros.WellDefinednessMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.WhileInvariantRule;

import org.key_project.prover.rules.RuleAbortException;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;


@NullMarked
public class WdWhileInvariantRule extends WhileInvariantRule {
    @Override
    public @NonNull ImmutableList<Goal> apply(Goal goal, RuleApp ruleApp)
            throws RuleAbortException {
        return new WdWhileInvariantRuleApplier(goal, (LoopInvariantBuiltInRuleApp<?>) ruleApp)
                .apply();
    }

    protected static class WdWhileInvariantRuleApplier extends WhileInvariantRuleApplier {
        public WdWhileInvariantRuleApplier(Goal goal, LoopInvariantBuiltInRuleApp<?> ruleApp) {
            super(goal, ruleApp);
        }

        @Override
        public @NonNull ImmutableList<Goal> apply() {
            final ImmutableList<Goal> result = goal.split(4);
            prepareGoals(result);
            setupWdGoal(result.get(3));
            return result;

        }

        private void setupWdGoal(Goal goal) {
            goal.setBranchLabel(WellDefinednessMacro.WD_BRANCH);
            final LoopWellDefinedness lwd = new LoopWellDefinedness(inst.inv(), localIns, services);
            final LocationVariable self;
            if (inst.selfTerm().op() instanceof LocationVariable lv) {
                self = lv;
            } else {
                self = null;
            }
            services.getSpecificationRepository().addWdStatement(lwd);
            LocationVariable heap = heapContext.getFirst();
            final SequentFormula wdInv = lwd.generateSequent(self, heap, anonHeap, localIns,
                inst.u(), localAnonUpdate, services);
            goal.changeFormula(wdInv, ruleApp.posInOccurrence());
        }
    }
}
