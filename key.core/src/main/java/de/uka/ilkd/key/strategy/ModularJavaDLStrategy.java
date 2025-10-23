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
import de.uka.ilkd.key.strategy.termProjection.FocusProjection;

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

/// Combines a list of strategies into a unified strategy. Theory combination
/// is based on the costs computed by each component strategy. Age of the rule
/// application is used to ensure that any applicable rule will eventually be
/// applied.
///
/// Conflicts (i.e., when more than one component strategy provides a cost
/// computation for one rule set) have to be resolved explicitly by declaring
/// a conflict resolution [#resolveConflict(RuleSetDispatchFeature, RuleSet, List)].
///
/// Do not create directly. Use [ModularJavaDLStrategyFactory] instead.
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
        return conflictCostDispatcher;
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
                var folStrat = value.getFirst();
                var intStrat = value.get(1);
                bindRuleSet(d, "order_terms",
                    ifZero(applyTF("commEqLeft", tf.intF),
                        intStrat.getCostDispatcher().remove(rs),
                        folStrat.getCostDispatcher().remove(rs)));
            }
            case "apply_equations" -> {
                var folStrat = value.getFirst();
                var intStrat = value.get(1);
                bindRuleSet(d, "apply_equations",
                    ifZero(applyTF(FocusProjection.create(0), tf.intF),
                        intStrat.getCostDispatcher().remove(rs),
                        folStrat.getCostDispatcher().remove(rs)));
            }
            case "apply_equations_andOr" -> {
                var folStrat = value.getFirst();
                var intStrat = value.get(1);
                if (quantifierInstantiatedEnabled()) {
                    bindRuleSet(d, "apply_equations_andOr",
                        ifZero(applyTF(FocusProjection.create(0), tf.intF),
                            intStrat.getCostDispatcher().remove(rs),
                            folStrat.getCostDispatcher().remove(rs)));
                } else {
                    bindRuleSet(d, "apply_equations_andOr", inftyConst());
                }
            }
            default -> throw new IllegalArgumentException("No resolution defined for " + rs);
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

    private boolean quantifierInstantiatedEnabled() {
        return !StrategyProperties.QUANTIFIERS_NONE
                .equals(strategyProperties.getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY));
    }
}
