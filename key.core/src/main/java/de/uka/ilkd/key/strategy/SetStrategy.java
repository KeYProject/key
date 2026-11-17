/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy;


import de.uka.ilkd.key.ldt.SetLDT;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.feature.SetsSmallerThanFeature;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.IBuiltInRule;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.AbstractFeatureStrategy;
import org.key_project.prover.strategy.ComponentStrategy;
import org.key_project.prover.strategy.costbased.CostBand;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.feature.MatchedAssumesFeature;
import org.key_project.prover.strategy.costbased.feature.RuleSetDispatchFeature;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

import org.jspecify.annotations.NonNull;

import static de.uka.ilkd.key.strategy.SetCosts.COMMUTE;
import static de.uka.ilkd.key.strategy.SetCosts.DIST;

/// Strategy for the sort generic theory of sets.
/// Do not create directly; use [SetStrategyFactory] instead.
public class SetStrategy extends AbstractFeatureStrategy<Goal> implements ComponentStrategy<Goal> {
    public static final Name NAME = new Name("Set Strategy");


    private final boolean stopAtFirstNonCloseableGoal;
    private final SetTermFeatures stf;
    private final Proof proof;

    public SetStrategy(Proof proof, StrategyProperties strategyProperties) {
        this.proof = proof;
        stf = new SetTermFeatures(proof.getServices().getTypeConverter().getLDT(SetLDT.class));
        setupCostComputationF(costComputationDispatcher);

        stopAtFirstNonCloseableGoal =
            strategyProperties.getProperty(StrategyProperties.STOPMODE_OPTIONS_KEY)
                    .equals(StrategyProperties.STOPMODE_NONCLOSE);
    }

    private void setupCostComputationF(RuleSetDispatchFeature d) {
        bindRuleSet(d, "setEqualityBlastingRight", CostBand.DEFAULT.at(-90));

        // Distribution duplicates the distributed set, so it is allowed only
        // where a resulting set is known to collapse.
        final TermFeature collapses = or(stf.emptyF, stf.singletonF);
        final Feature operandCollapses = or(applyTF("distributedSet", collapses),
            applyTF("unionLeft", collapses), applyTF("unionRight", collapses));
        bindRuleSet(d, "setDist",
            add(ifZero(MatchedAssumesFeature.create(), operandCollapses, CostBand.DEFAULT.cost()),
                longConst(DIST)));

        bindRuleSet(d, "setAssoc", longConst(-850));

        // Always on, independent of the quantifier treatment: e.g. union(l, s) = union(s, l)
        // closes after one swap where it would otherwise need blasting the sets.
        bindRuleSet(d, "setComm",
            add(applyTF("commLeft", not(or(stf.unionF, stf.intersectF))),
                applyTF("commRight", not(or(stf.unionF, stf.intersectF))),
                SetsSmallerThanFeature.create(instOf("commRight"), instOf("commLeft"), stf,
                    JavaStaticFeatureCollection.createTermOrdering()),
                longConst(COMMUTE)));
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return stopAtFirstNonCloseableGoal;
    }

    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        return true;
    }

    @Override
    public RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
            MutableState mState) {
        return longConst(0).computeCost(app, pio, goal, mState);
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, ProofGoal<?> goal, MutableState mState) {
        return this.costComputationDispatcher.computeCost(app, pos, goal, mState);
    }

    @Override
    public boolean isResponsibleFor(IBuiltInRule<Goal> rule) {
        return false;
    }

    // TODO: Unify in class?
    @Override
    protected RuleSet getHeuristic(String p_name) {
        final NamespaceSet nss = proof.getNamespaces();
        final Namespace<@NonNull RuleSet> ns = nss.ruleSets();
        final RuleSet h = ns.lookup(new Name(p_name));

        assert h != null : "Did not find the rule set " + p_name;

        return h;
    }

    @Override
    protected LogicServices getServices() {
        return proof.getServices();
    }
}
