/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.ArrayList;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Function;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.feature.AgeFeature;
import de.uka.ilkd.key.strategy.feature.MatchedAssumesFeature;
import de.uka.ilkd.key.strategy.feature.NonDuplicateAppFeature;

import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
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

    public ModularJavaDLStrategy(Proof proof, StrategyProperties properties) {
        super(proof);
        strategies.add(new IntegerStrategy(proof, properties));
        strategies.add(new StringStrategy(proof, properties));
        strategies.add(new JavaCardDLStrategy(proof, properties));
        reduceCostTillMaxF = new ReduceCostTillMaxFeature();
        reduceInstTillMaxF = new ReduceInstTillMaxFeature();
        this.strategyProperties = (StrategyProperties) properties.clone();
    }

    @Override
    protected RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
            MutableState mState) {
        // TODO: enable
        final Feature ifMatchedF = ifZero(MatchedAssumesFeature.INSTANCE, longConst(+1));
        Feature totalCost =
            add(AutomatedRuleFeature.getInstance(), NonDuplicateAppFeature.INSTANCE,
                reduceInstTillMaxF,
                AgeFeature.INSTANCE, ifMatchedF);
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
            Function<AbstractFeatureStrategy, R> mapper) {
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
        Feature totalCost =
            add(AutomatedRuleFeature.getInstance(), NonDuplicateAppFeature.INSTANCE,
                reduceCostTillMaxF,
                AgeFeature.INSTANCE, ifMatchedF);
        return totalCost.computeCost(app, pos, goal, mState);
    }

    private class ReduceCostTillMaxFeature implements Feature {
        @Override
        public <GOAL extends ProofGoal<@NonNull GOAL>> RuleAppCost computeCost(RuleApp app,
                PosInOccurrence pos, GOAL goal, MutableState mState) {
            return reduceTillMax(app, NumberRuleAppCost.getZeroCost(), TopRuleAppCost.INSTANCE,
                RuleAppCost::add, s -> s.computeCost(app, pos, goal, mState));
        }
    }

    private class ReduceInstTillMaxFeature implements Feature {
        @Override
        public <GOAL extends ProofGoal<@NonNull GOAL>> RuleAppCost computeCost(RuleApp app,
                PosInOccurrence pos, GOAL goal, MutableState mState) {
            return reduceTillMax(app, NumberRuleAppCost.getZeroCost(), TopRuleAppCost.INSTANCE,
                RuleAppCost::add, s -> s.instantiateApp(app, pos, (Goal) goal, mState));
        }
    }
}
