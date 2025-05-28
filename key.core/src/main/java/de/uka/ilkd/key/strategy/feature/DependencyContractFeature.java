/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.speclang.HeapContext;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.BinaryFeature;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;

public final class DependencyContractFeature extends BinaryFeature {

    private void removePreviouslyUsedSteps(JTerm focus, Goal goal,
            List<PosInOccurrence> steps) {
        for (RuleApp app : goal.appliedRuleApps()) {
            JTerm term = (JTerm) app.posInOccurrence().subTerm();
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
    protected <Goal extends ProofGoal<@NonNull Goal>> boolean filter(RuleApp app,
            PosInOccurrence pos,
            Goal p_goal, MutableState mState) {
        IBuiltInRuleApp bapp = (IBuiltInRuleApp) app;
        final JTerm focus = (JTerm) pos.subTerm();

        // determine possible steps
        final var goal = (de.uka.ilkd.key.proof.Goal) p_goal;
        final Services services = goal.proof().getServices();
        List<LocationVariable> heapContext = bapp.getHeapContext() != null ? bapp.getHeapContext()
                : HeapContext.getModifiableHeaps(services, false);

        final List<PosInOccurrence> steps =
            UseDependencyContractRule.getSteps(heapContext, pos, goal.sequent(), services);
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
