/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.ldt.SetLDT;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.strategy.feature.MatchedAssumesFeature;
import de.uka.ilkd.key.strategy.feature.RuleSetDispatchFeature;
import de.uka.ilkd.key.strategy.feature.SetsSmallerThanFeature;

import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.CostBand;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.strategy.SetCosts.COMMUTE;
import static de.uka.ilkd.key.strategy.SetCosts.DIST;

/// Strategy for the sort generic theory of sets.
/// Do not create directly; use [SetStrategyFactory] instead.
public class SetStrategy extends AbstractFeatureStrategy implements ComponentStrategy {
    public static final Name NAME = new Name("Set Strategy");

    private final RuleSetDispatchFeature costComputationDispatcher;

    private final boolean stopAtFirstNonCloseableGoal;
    private final SetTermFeatures stf;

    public SetStrategy(Proof proof, StrategyProperties strategyProperties) {
        super(proof);
        stf = new SetTermFeatures(getServices().getTypeConverter().getLDT(SetLDT.class));
        costComputationDispatcher = setupCostComputationF();

        stopAtFirstNonCloseableGoal =
            strategyProperties.getProperty(StrategyProperties.STOPMODE_OPTIONS_KEY)
                    .equals(StrategyProperties.STOPMODE_NONCLOSE);
    }

    private RuleSetDispatchFeature setupCostComputationF() {
        final RuleSetDispatchFeature d = new RuleSetDispatchFeature();
        bindRuleSet(d, "setEqualityBlastingRight", CostBand.DEFAULT.at(-90));

        // Distribution duplicates the distributed set, so it is allowed only
        // where a resulting set is known to collapse.
        final TermFeature collapses = or(stf.emptyF, stf.singletonF);
        final Feature operandCollapses = or(applyTF("distributedSet", collapses),
            applyTF("unionLeft", collapses), applyTF("unionRight", collapses));
        bindRuleSet(d, "setDist",
            add(ifZero(MatchedAssumesFeature.INSTANCE, operandCollapses, CostBand.DEFAULT.cost()),
                longConst(DIST)));

        bindRuleSet(d, "setAssoc", longConst(-850));

        // Always on, independent of the quantifier treatment: e.g. union(l, s) = union(s, l)
        // closes after one swap where it would otherwise need blasting the sets.
        bindRuleSet(d, "setComm",
            add(applyTF("commLeft", not(or(stf.unionF, stf.intersectF))),
                applyTF("commRight", not(or(stf.unionF, stf.intersectF))),
                SetsSmallerThanFeature.create(instOf("commRight"), instOf("commLeft"), stf),
                longConst(COMMUTE)));
        return d;
    }

    @Override
    public boolean isResponsibleFor(RuleSet rs) {
        return costComputationDispatcher.get(rs) != null;
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
    public <GOAL extends ProofGoal<@NonNull GOAL>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, GOAL goal, MutableState mState) {
        return this.costComputationDispatcher.computeCost(app, pos, goal, mState);
    }

    @Override
    public Set<RuleSet> getResponsibilities(StrategyAspect aspect) {
        var set = new HashSet<RuleSet>();
        RuleSetDispatchFeature dispatcher = getDispatcher(aspect);
        if (dispatcher != null) {
            set.addAll(dispatcher.ruleSets());
        }
        return set;
    }

    @Override
    public @Nullable RuleSetDispatchFeature getDispatcher(StrategyAspect aspect) {
        return aspect == StrategyAspect.Cost ? costComputationDispatcher : null;
    }

    @Override
    public boolean isResponsibleFor(BuiltInRule rule) {
        return false;
    }
}
