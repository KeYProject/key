/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.feature.RuleSetDispatchFeature;
import de.uka.ilkd.key.strategy.feature.instantiator.ForEachCP;
import de.uka.ilkd.key.strategy.feature.instantiator.OneOfCP;
import de.uka.ilkd.key.strategy.feature.instantiator.SVInstantiationCP;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.prover.proof.rulefilter.IHTacletFilter;
import org.key_project.prover.proof.rulefilter.TacletFilter;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.ConditionalFeature;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.feature.instantiator.BackTrackingManager;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;
import org.key_project.prover.strategy.costbased.termProjection.TermBuffer;
import org.key_project.prover.strategy.costbased.termgenerator.TermGenerator;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;

public abstract class AbstractFeatureStrategy extends StaticFeatureCollection
        implements Strategy<Goal> {

    private final Proof proof;

    protected AbstractFeatureStrategy(Proof proof) {
        this.proof = proof;
    }

    /**
     * @return Returns the proof.
     */
    protected Proof getProof() {
        return proof;
    }

    /**
     * @param heuristics
     * @param thenFeature
     * @return the conditional feature return true when the rule belongs to one of the given
     *         heuristics
     */
    protected Feature ifHeuristics(String[] heuristics, Feature thenFeature) {
        return ConditionalFeature.createConditional(getFilterFor(heuristics), thenFeature);
    }

    protected Feature ifHeuristics(String[] heuristics, Feature thenFeature,
            Feature elseFeature) {
        return ConditionalFeature.createConditional(getFilterFor(heuristics), thenFeature,
            elseFeature);
    }

    protected Feature ifHeuristics(String[] names, int priority) {
        return ConditionalFeature.createConditional(getFilterFor(names), cost(priority), cost(0));
    }

    protected TacletFilter getFilterFor(String[] p_names) {
        ImmutableList<RuleSet> heur = ImmutableSLList.nil();
        for (int i = 0; i != p_names.length; ++i) {
            heur = heur.prepend(getHeuristic(p_names[i]));
        }
        return new IHTacletFilter(false, heur);
    }

    protected RuleSet getHeuristic(String p_name) {
        final NamespaceSet nss = getProof().getNamespaces();
        final Namespace<@NonNull RuleSet> ns = nss.ruleSets();
        final RuleSet h = ns.lookup(new Name(p_name));

        assert h != null : "Did not find the rule set " + p_name;

        return h;
    }

    protected void bindRuleSet(RuleSetDispatchFeature d, RuleSet ruleSet, Feature f) {
        d.add(ruleSet, f);
    }

    protected void bindRuleSet(RuleSetDispatchFeature d, RuleSet ruleSet, long cost) {
        bindRuleSet(d, ruleSet, longConst(cost));
    }

    protected void bindRuleSet(RuleSetDispatchFeature d, String ruleSet, Feature f) {
        bindRuleSet(d, getHeuristic(ruleSet), f);
    }

    protected void bindRuleSet(RuleSetDispatchFeature d, String ruleSet, long cost) {
        bindRuleSet(d, getHeuristic(ruleSet), longConst(cost));
    }

    protected void clearRuleSetBindings(RuleSetDispatchFeature d, RuleSet ruleSet) {
        d.clear(ruleSet);
    }

    protected void clearRuleSetBindings(RuleSetDispatchFeature d, String ruleSet) {
        d.clear(getHeuristic(ruleSet));
    }


    @Override
    public void instantiateApp(RuleApp app, PosInOccurrence pio,
            Goal goal,
            RuleAppCostCollector collector) {
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

    protected abstract RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
            MutableState mState);

    protected Feature forEach(TermBuffer<Goal> x, TermGenerator<Goal> gen, Feature body) {
        return ForEachCP.create(x, gen, body);
    }

    protected Feature oneOf(Feature[] features) {
        return OneOfCP.create(features);
    }

    protected Feature oneOf(Feature feature0, Feature feature1) {
        // noinspection unchecked
        return oneOf(new Feature[] { feature0, feature1 });
    }

    // it is possible to turn off the method <code>instantiate</code>,
    // which can be useful in order to use the same feature definitions both for
    // cost computation and instantiation

    private boolean instantiateActive = false;

    protected void enableInstantiate() {
        instantiateActive = true;
    }

    protected void disableInstantiate() {
        instantiateActive = false;
    }

    protected Feature instantiate(Name sv, ProjectionToTerm<Goal> value) {
        if (instantiateActive) {
            return SVInstantiationCP.create(sv, value);
        } else {
            return longConst(0);
        }
    }

    protected Feature instantiateTriggeredVariable(ProjectionToTerm<Goal> value) {
        if (instantiateActive) {
            return SVInstantiationCP.createTriggeredVarCP(value);
        } else {
            return longConst(0);
        }
    }

    protected Feature instantiate(String sv, ProjectionToTerm<Goal> value) {
        return instantiate(new Name(sv), value);
    }
}
