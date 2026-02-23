/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.ComponentStrategy.StrategyAspect;
import de.uka.ilkd.key.strategy.feature.AgeFeature;
import de.uka.ilkd.key.strategy.feature.MatchedAssumesFeature;
import de.uka.ilkd.key.strategy.feature.NonDuplicateAppFeature;
import de.uka.ilkd.key.strategy.feature.RuleSetDispatchFeature;
import de.uka.ilkd.key.strategy.termProjection.FocusProjection;

import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.Rule;
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

/// Combines a list of component strategies [ComponentStrategy] into a unified strategy. Theory
/// combination
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

    /// List of component strategies. Order is not strictly important.
    private final List<ComponentStrategy> strategies = new ArrayList<>();
    private final StrategyProperties strategyProperties;

    private final Feature reduceInstTillMaxF;
    private final ArithTermFeatures tf;
    private final Feature totalCost;

    private final ResponsibleStrategyCache responsibleStrategyCache;

    public ModularJavaDLStrategy(Proof proof, List<ComponentStrategy> componentStrategies,
            StrategyProperties properties) {
        super(proof);
        strategies.addAll(componentStrategies);
        this.strategyProperties = (StrategyProperties) properties.clone();
        this.tf = new ArithTermFeatures(getServices().getTypeConverter().getIntegerLDT());

        responsibleStrategyCache = new ResponsibleStrategyCache(strategies);

        // if more than one strategy is responsible for a _ruleset_ we need to determine how to
        // resolve the
        // competing computations
        RuleSetDispatchFeature conflictCostDispatcher = resolveConflicts();

        final Feature ifMatchedF = ifZero(MatchedAssumesFeature.INSTANCE, longConst(+1));
        Feature reduceCostTillMaxF = new ReduceTillMaxFeature(Feature::computeCost,
            (rule) -> responsibleStrategyCache.getResponsibleStrategies(rule, strategies,
                StrategyAspect.Cost));

        reduceInstTillMaxF = new ReduceTillMaxFeature(ComponentStrategy::instantiateApp,
            (rule) -> responsibleStrategyCache.getResponsibleStrategies(rule, strategies,
                StrategyAspect.Instantiation));

        // the feature for the cost computation
        totalCost =
            add(AutomatedRuleFeature.getInstance(), ifMatchedF, NonDuplicateAppFeature.INSTANCE,
                reduceCostTillMaxF, conflictCostDispatcher, AgeFeature.INSTANCE);
    }

    private record StratAndDispatcher(ComponentStrategy strategy,
            RuleSetDispatchFeature dispatcher) {
    }

    /**
     * checks for conflicts and resolves known ones (in case an unknown conflict is encountered the
     * method fails with a runtime exception
     *
     * @return the feature implementing the conflict resolution
     */
    private RuleSetDispatchFeature resolveConflicts() {
        var dis = new RuleSetDispatchFeature();
        var dispatchers =
            strategies.stream()
                    .map(s -> new StratAndDispatcher(s, s.getDispatcher(StrategyAspect.Cost)))
                    .toList();
        var map = new HashMap<RuleSet, List<Name>>();
        for (var d : dispatchers) {
            var s = d.strategy;
            for (var rs : d.dispatcher.ruleSets()) {
                var lst = map.computeIfAbsent(rs, r -> new ArrayList<>());
                lst.add(s.name());
            }
        }
        for (var e : map.entrySet()) {
            if (e.getValue().size() > 1) {
                resolveConflict(dis, e.getKey());
            }
        }
        return dis;
    }

    /**
     * resolves known conflicts
     *
     * @param d the RuleSetDispatchFeature to which the conflict resolution will be bound
     * @param rs the RuleSet for which a conflict resolution is required
     * @throws IllegalArgumentException if the conflict cannot be resolved
     */
    private void resolveConflict(RuleSetDispatchFeature d, RuleSet rs) {
        var folStrat = responsibleStrategyCache.getStrategyByName(JFOLStrategy.NAME);
        var intStrat = responsibleStrategyCache.getStrategyByName(IntegerStrategy.NAME);
        switch (rs.name().toString()) {
            case "order_terms" -> {
                bindRuleSet(d, "order_terms",
                    ifZero(applyTF("commEqLeft", tf.intF),
                        intStrat.getDispatcher(StrategyAspect.Cost).remove(rs),
                        folStrat.getDispatcher(StrategyAspect.Cost).remove(rs)));
            }
            case "apply_equations" -> {
                bindRuleSet(d, "apply_equations",
                    ifZero(applyTF(FocusProjection.create(0), tf.intF),
                        intStrat.getDispatcher(StrategyAspect.Cost).remove(rs),
                        folStrat.getDispatcher(StrategyAspect.Cost).remove(rs)));
            }
            case "apply_equations_andOr" -> {
                if (quantifierInstantiatedEnabled()) {
                    bindRuleSet(d, "apply_equations_andOr",
                        ifZero(applyTF(FocusProjection.create(0), tf.intF),
                            intStrat.getDispatcher(StrategyAspect.Cost).remove(rs),
                            folStrat.getDispatcher(StrategyAspect.Cost).remove(rs)));
                } else {
                    bindRuleSet(d, "apply_equations_andOr", inftyConst());
                }
            }
            default -> throw new IllegalArgumentException("No resolution defined for " + rs);
        }
    }

    @Override
    public RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
            MutableState mState) {
        enableInstantiate();
        final Feature ifMatchedF = ifZero(MatchedAssumesFeature.INSTANCE, longConst(+1));
        final Feature conflictCostDispatcher = resolveConflicts();
        final Feature totalCost =
            add(AutomatedRuleFeature.getInstance(), ifMatchedF, NonDuplicateAppFeature.INSTANCE,
                conflictCostDispatcher, reduceInstTillMaxF, AgeFeature.INSTANCE);
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
        if (!isApproved) {
            return false;
        }
        return reduceTillMax(isApproved, false, Boolean::logicalAnd,
            s -> s.isApprovedApp(app, pio, goal),
            responsibleStrategyCache.getResponsibleStrategies(app.rule(),
                strategies, StrategyAspect.Approval));
    }

    @Override
    public Name name() {
        return NAME;
    }

    /// A reducer method that accumulates something computed by strategies, e.g., cost or approval
    /// (boolean)
    /// and stops once the maximum is reached (top cost or `false`).
    /// @param <R> the result type to be accumulated
    /// @param init initial value
    /// @param max the maximal value; once reached, nothing further is computed
    /// @param accumulator accumulator function
    /// @param mapper maps a strategy to the required value (cost/approval); e.g.,
    /// [ComponentStrategy#computeCost(RuleApp, PosInOccurrence, ProofGoal)]
    /// @param strats the relevant [ComponentStrategy]s for this computation
    private <R> R reduceTillMax(R init, R max, BiFunction<R, R, R> accumulator,
            Function<ComponentStrategy, R> mapper, LinkedHashSet<ComponentStrategy> strats) {
        for (ComponentStrategy strategy : strats) {
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
        return totalCost.computeCost(app, pos, goal, mState);
    }

    @FunctionalInterface
    private interface StrategyCostFunction {
        RuleAppCost compute(ComponentStrategy strategy, RuleApp app,
                PosInOccurrence pos, Goal goal, MutableState mState);
    }

    /// A [Feature] that computes a [RuleAppCost] as defined in
    /// [ModularJavaDLStrategy#reduceInstTillMaxF].
    private class ReduceTillMaxFeature implements Feature {
        /// A function to get the relevant [RuleAppCost] (i.e., [Feature#computeCost(RuleApp,
        /// PosInOccurrence, ProofGoal, MutableState)] or
        /// [ComponentStrategy#instantiateApp(RuleApp, PosInOccurrence, Goal, MutableState)]).
        private final StrategyCostFunction mapper;
        /// A function to get the relevant strategies for a [Rule]
        private final Function<Rule, LinkedHashSet<ComponentStrategy>> ruleToStrategy;

        ReduceTillMaxFeature(StrategyCostFunction mapper,
                Function<Rule, LinkedHashSet<ComponentStrategy>> ruleToStrategy) {
            this.mapper = mapper;
            this.ruleToStrategy = ruleToStrategy;
        }

        @Override
        public <GOAL extends ProofGoal<@NonNull GOAL>> RuleAppCost computeCost(RuleApp app,
                PosInOccurrence pos, GOAL goal, MutableState mState) {
            return reduceTillMax(NumberRuleAppCost.getZeroCost(), TopRuleAppCost.INSTANCE,
                RuleAppCost::add, s -> mapper.compute(s, app, pos, (Goal) goal, mState),
                ruleToStrategy.apply(app.rule()));
        }
    }

    private boolean quantifierInstantiatedEnabled() {
        return !StrategyProperties.QUANTIFIERS_NONE
                .equals(strategyProperties.getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY));
    }
}
