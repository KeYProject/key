/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy;

import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.feature.RuleSetDispatchFeature;
import org.key_project.prover.strategy.costbased.feature.instantiator.BackTrackingManager;
import org.key_project.prover.strategy.costbased.feature.instantiator.ForEachCP;
import org.key_project.prover.strategy.costbased.feature.instantiator.OneOfCP;
import org.key_project.prover.strategy.costbased.feature.instantiator.SVInstantiationCP;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;
import org.key_project.prover.strategy.costbased.termProjection.TermBuffer;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;
import org.key_project.prover.strategy.costbased.termgenerator.TermGenerator;

public abstract class AbstractFeatureStrategy<G extends ProofGoal<G>>
        extends StaticFeatureCollection implements Strategy<G> {
    /// It is possible to turn off the method <code>instantiate</code>,
    /// which can be useful in order to use the same feature definitions both for
    /// cost computation and instantiation.
    ///
    /// Counts nesting depth of instantiation activation to avoid premature deactivation.
    private short instantiateActive = 0;

    protected void enableInstantiate() {
        instantiateActive++;
        assert instantiateActive >= 0 : "overflow occurred";
    }

    protected void disableInstantiate() {
        instantiateActive--;
        assert instantiateActive >= 0;
    }

    protected void bindRuleSet(RuleSetDispatchFeature d, RuleSet ruleSet, Feature f) {
        d.add(ruleSet, f);
    }

    protected void bindRuleSet(RuleSetDispatchFeature d, String ruleSet, Feature f) {
        bindRuleSet(d, getHeuristic(ruleSet), f);
    }

    protected void bindRuleSet(RuleSetDispatchFeature d, String ruleSet, long cost) {
        bindRuleSet(d, getHeuristic(ruleSet), longConst(cost));
    }

    protected void clearRuleSetBindings(RuleSetDispatchFeature d, String ruleSet) {
        d.clear(getHeuristic(ruleSet));
    }

    protected abstract RuleSet getHeuristic(String p_name);

    protected Feature instantiate(String sv, ProjectionToTerm<G> value) {
        return instantiate(new Name(sv), value);
    }

    protected Feature instantiate(Name sv, ProjectionToTerm<G> value) {
        if (instantiateActive != 0) {
            return SVInstantiationCP.create(sv, value);
        } else {
            return longConst(0);
        }
    }

    protected Feature forEach(TermBuffer<G> x, TermGenerator<G> gen, Feature body) {
        return ForEachCP.create(x, gen, body);
    }

    protected Feature oneOf(Feature[] features) {
        return OneOfCP.create(features);
    }

    protected abstract Feature isBelow(TermFeature t);

    @Override
    public void instantiateApp(RuleApp app, PosInOccurrence pio,
            G goal,
            org.key_project.prover.strategy.RuleAppCostCollector collector) {
        final MutableState mState = new MutableState();
        final BackTrackingManager btManager = mState.getBacktrackingManager();
        btManager.setup(app);
        do {
            final RuleAppCost cost = instantiateApp(app, pio, goal, mState);
            if (cost instanceof TopRuleAppCost) {
                continue;
            }
            final RuleApp res = btManager.getResultingapp();
            if (res == app || res == null) {
                continue;
            }
            collector.collect(res, cost);
        } while (btManager.backtrack());
    }
}
