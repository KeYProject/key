/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import java.util.List;

import de.uka.ilkd.key.java.Services;
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
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;


public final class DependencyContractFeature extends BinaryFeature {

    @Override
    protected <Goal extends ProofGoal<@NonNull Goal>> boolean filter(RuleApp app,
            PosInOccurrence pos,
            Goal p_goal, MutableState mState) {
        IBuiltInRuleApp bapp = (IBuiltInRuleApp) app;

        final var goal = (de.uka.ilkd.key.proof.Goal) p_goal;
        final Services services = goal.proof().getServices();
        List<LocationVariable> heapContext = bapp.getHeapContext() != null ? bapp.getHeapContext()
                : HeapContext.getModifiableHeaps(services, false);

        // the rule's step policy, shared with the completion of the application, see chooseStep
        final PosInOccurrence step =
            UseDependencyContractRule.chooseStep(pos, goal, heapContext, services);
        if (step == null) {
            return false;
        }

        bapp = bapp.setAssumesInsts(ImmutableList.singleton(step));
        return true;
    }
}
