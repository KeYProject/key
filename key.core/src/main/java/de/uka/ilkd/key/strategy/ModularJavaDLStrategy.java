/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Function;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.feature.AgeFeature;
import de.uka.ilkd.key.strategy.feature.MatchedAssumesFeature;
import de.uka.ilkd.key.strategy.feature.NonDuplicateAppFeature;
import de.uka.ilkd.key.strategy.feature.RuleSetDispatchFeature;

import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.AutomatedRuleFeature;
import org.key_project.prover.strategy.costbased.feature.Feature;

import org.jspecify.annotations.NonNull;

public class ModularJavaDLStrategy extends AbstractFeatureStrategy {
    public static final Name NAME = new Name("Modular JavaDL Strategy");

    private final List<AbstractFeatureStrategy> strategies = new ArrayList<>();
    private final StrategyProperties strategyProperties;
    private final Feature reduceCostTillMaxF;
    private final Feature reduceInstTillMaxF;
    private final ArithTermFeatures tf;
    private final RuleSetDispatchFeature conflictCostDispatcher;

    public ModularJavaDLStrategy(Proof proof, List<AbstractFeatureStrategy> componentStrategies,
            StrategyProperties properties) {
        super(proof);
        strategies.addAll(componentStrategies);
        reduceCostTillMaxF = new ReduceTillMaxFeature(Feature::computeCost);
        reduceInstTillMaxF = new ReduceTillMaxFeature(AbstractFeatureStrategy::instantiateApp);
        this.strategyProperties = (StrategyProperties) properties.clone();
        this.tf = new ArithTermFeatures(getServices().getTypeConverter().getIntegerLDT());
        conflictCostDispatcher = resolveConflicts();
    }

    @Override
    protected RuleSetDispatchFeature getCostDispatcher() {
        return null;
    }

    private record StratAndDispatcher(AbstractFeatureStrategy strategy,
            RuleSetDispatchFeature dispatcher) {
    }

    private RuleSetDispatchFeature resolveConflicts() {
        var dis = new RuleSetDispatchFeature();
        var dispatchers =
            strategies.stream().map(s -> new StratAndDispatcher(s, s.getCostDispatcher())).toList();
        var map = new HashMap<RuleSet, List<AbstractFeatureStrategy>>();
        for (var d : dispatchers) {
            var s = d.strategy;
            for (var rs : d.dispatcher.ruleSets()) {
                var lst = map.computeIfAbsent(rs, r -> new ArrayList<>());
                lst.add(s);
            }
        }
        for (var e : map.entrySet()) {
            if (e.getValue().size() > 1) {
                resolveConflict(dis, e.getKey(), e.getValue());
            }
        }
        return dis;
    }

    private void resolveConflict(RuleSetDispatchFeature d, RuleSet rs,
            List<AbstractFeatureStrategy> value) {
        switch (rs.name().toString()) {
        case "order_terms" -> {
            var intStrat = value.getFirst();
            var javaDLStrat = value.get(1);
            bindRuleSet(d, "order_terms",
                ifZero(applyTF("commEqLeft", tf.intF),
                    intStrat.getCostDispatcher().remove(rs),
                    javaDLStrat.getCostDispatcher().remove(rs)));
        }
        }
    }

    @Override
    protected RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
            MutableState mState) {
        enableInstantiate();
        final Feature ifMatchedF = ifZero(MatchedAssumesFeature.INSTANCE, longConst(+1));
        Feature totalCost =
            add(AutomatedRuleFeature.getInstance(), NonDuplicateAppFeature.INSTANCE,
                reduceInstTillMaxF,
                AgeFeature.INSTANCE, ifMatchedF);
        disableInstantiate();
        return totalCost.computeCost(app, pio, goal, mState);
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return strategyProperties.getProperty(StrategyProperties.STOPMODE_OPTIONS_KEY)
                .equals(StrategyProperties.STOPMODE_NONCLOSE);
    }

    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        boolean isApproved =
            NonDuplicateAppFeature.INSTANCE.computeCost(app, pio, goal,
                new MutableState()) != TopRuleAppCost.INSTANCE;
        return reduceTillMax(app, isApproved, false, Boolean::logicalAnd,
            s -> s.isApprovedApp(app, pio, goal));
    }

    @Override
    public Name name() {
        return NAME;
    }

    private <R> R reduceTillMax(RuleApp app, R init, R max, BiFunction<R, R, R> accumulator,
            Function<AbstractFeatureStrategy, R> mapper, Object... conflict) {
        for (AbstractFeatureStrategy strategy : strategies) {
            var isResponsible = false;
            var ruleSets = app.rule().ruleSets();
            if (!ruleSets.hasNext())
                isResponsible = true;
            else {
                while (ruleSets.hasNext()) {
                    var rs = ruleSets.next();
                    if (strategy.isResponsibleFor(rs)) {
                        isResponsible = true;
                        break;
                    }
                }
            }
            if (!isResponsible) {
                continue;
            }
            init = accumulator.apply(init, mapper.apply(strategy));
            if (init == max) {
                break;
            }
        }
        return init;
    }

    @Override
    public <GOAL extends ProofGoal<@NonNull GOAL>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, GOAL goal, MutableState mState) {
        final Feature ifMatchedF = ifZero(MatchedAssumesFeature.INSTANCE, longConst(+1));
        // TODO: This could be inefficient. Maybe we can simplify conflict resolution
        Feature totalCost =
            add(AutomatedRuleFeature.getInstance(), NonDuplicateAppFeature.INSTANCE,
                reduceCostTillMaxF, conflictCostDispatcher,
                AgeFeature.INSTANCE, ifMatchedF);
        return totalCost.computeCost(app, pos, goal, mState);
    }

    @FunctionalInterface
    private interface StrategyCostFunction {
        RuleAppCost compute(AbstractFeatureStrategy strategy, RuleApp app,
                PosInOccurrence pos, Goal goal, MutableState mState);
    }

    private class ReduceTillMaxFeature implements Feature {
        private final StrategyCostFunction mapper;

        ReduceTillMaxFeature(StrategyCostFunction mapper) {
            this.mapper = mapper;
        }

        @Override
        public <GOAL extends ProofGoal<@NonNull GOAL>> RuleAppCost computeCost(RuleApp app,
                PosInOccurrence pos, GOAL goal, MutableState mState) {
            return reduceTillMax(app, NumberRuleAppCost.getZeroCost(), TopRuleAppCost.INSTANCE,
                RuleAppCost::add, s -> mapper.compute(s, app, pos, (Goal) goal, mState));
        }
    }
}
