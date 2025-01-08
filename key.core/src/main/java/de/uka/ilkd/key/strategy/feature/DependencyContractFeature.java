/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import java.util.List;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.speclang.HeapContext;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableSLList;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;

public final class DependencyContractFeature extends BinaryFeature {

    private void removePreviouslyUsedSteps(Term focus, Goal goal,
            List<PosInOccurrence> steps) {
        for (org.key_project.prover.rules.RuleApp app : goal.appliedRuleApps()) {
            Term term = (Term) app.posInOccurrence().subTerm();
            if (app.rule() instanceof UseDependencyContractRule
                    && RENAMING_TERM_PROPERTY.equalsModThisProperty(term, focus)) {
                final IBuiltInRuleApp bapp = (IBuiltInRuleApp) app;
                for (PosInOccurrence ifInst : bapp.assumesInsts()) {
                    steps.remove(ifInst);
                }
            }
        }
    }

    @Override
    protected boolean filter(RuleApp app, PosInOccurrence pos,
            Goal goal, MutableState mState) {
        IBuiltInRuleApp bapp = (IBuiltInRuleApp) app;
        final Term focus = (Term) pos.subTerm();

        // determine possible steps

        List<LocationVariable> heapContext = bapp.getHeapContext() != null ? bapp.getHeapContext()
                : HeapContext.getModifiableHeaps(goal.proof().getServices(), false);

        final List<PosInOccurrence> steps =
            UseDependencyContractRule.getSteps(heapContext, pos,
                goal.sequent(), goal.proof().getServices());
        if (steps.isEmpty()) {
            return false;
        }

        // remove previously used steps
        removePreviouslyUsedSteps(focus, goal, steps);

        if (steps.isEmpty()) {
            return false;
        }

        if (pos.isTopLevel() && focus.sort() == JavaDLTheory.FORMULA
                && pos.isInAntec() == steps.get(0).isInAntec()) {
            return false;
        }

        // instantiate with arbitrary remaining step
        bapp = bapp.setAssumesInsts(ImmutableSLList.<PosInOccurrence>nil().prepend(steps.get(0)));
        return true;
    }
}
