/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import java.util.List;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.speclang.HeapContext;

import org.key_project.util.collection.ImmutableSLList;

public final class DependencyContractFeature extends BinaryFeature {

    private void removePreviouslyUsedSteps(Term focus, Goal goal, List<PosInOccurrence> steps) {
        for (RuleApp app : goal.appliedRuleApps()) {
            if (app.rule() instanceof UseDependencyContractRule
                    && app.posInOccurrence().subTerm().equalsModRenaming(focus)) {
                final IBuiltInRuleApp bapp = (IBuiltInRuleApp) app;
                for (PosInOccurrence ifInst : bapp.ifInsts()) {
                    steps.remove(ifInst);
                }
            }
        }
    }

    @Override
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        IBuiltInRuleApp bapp = (IBuiltInRuleApp) app;
        final Term focus = pos.subTerm();

        // determine possible steps

        List<LocationVariable> heapContext = bapp.getHeapContext() != null ? bapp.getHeapContext()
                : HeapContext.getModHeaps(goal.proof().getServices(), false);

        final List<PosInOccurrence> steps = UseDependencyContractRule.getSteps(heapContext, pos,
            goal.sequent(), goal.proof().getServices());
        if (steps.isEmpty()) {
            return false;
        }

        // remove previously used steps
        removePreviouslyUsedSteps(focus, goal, steps);

        if (steps.isEmpty()) {
            return false;
        }

        if (pos.isTopLevel() && focus.sort() == Sort.FORMULA
                && pos.isInAntec() == steps.get(0).isInAntec()) {
            return false;
        }

        // instantiate with arbitrary remaining step
        bapp = bapp.setIfInsts(ImmutableSLList.<PosInOccurrence>nil().prepend(steps.get(0)));
        return true;
    }
}
