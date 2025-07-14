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

import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;

import org.jspecify.annotations.NonNull;

public class ModularJavaDLStrategy extends AbstractFeatureStrategy {

    public static final Name NAME = new Name("Modular JavaDL Strategy");

    private final List<AbstractFeatureStrategy> strategies = new ArrayList<>();
    private final StrategyProperties strategyProperties;

    public ModularJavaDLStrategy(Proof proof, StrategyProperties properties) {
        super(proof);
        strategies.add(new IntegerStrategy(proof, properties));
        strategies.add(new StringStrategy(proof, properties));
        strategies.add(new JavaCardDLStrategy(proof, properties));
        this.strategyProperties = (StrategyProperties) properties.clone();
    }

    @Override
    protected RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
            MutableState mState) {
        return reduceTillMax(app, NumberRuleAppCost.getZeroCost(), TopRuleAppCost.INSTANCE,
            RuleAppCost::add, s -> s.instantiateApp(app, pio, goal, mState));
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return strategyProperties.getProperty(StrategyProperties.STOPMODE_OPTIONS_KEY)
                .equals(StrategyProperties.STOPMODE_NONCLOSE);
    }

    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        return reduceTillMax(app, true, false, Boolean::logicalAnd,
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
            if (!ruleSets.hasNext()) isResponsible = true;
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
        return reduceTillMax(app, NumberRuleAppCost.getZeroCost(), TopRuleAppCost.INSTANCE,
            RuleAppCost::add, s -> s.computeCost(app, pos, goal, mState));
    }
}
