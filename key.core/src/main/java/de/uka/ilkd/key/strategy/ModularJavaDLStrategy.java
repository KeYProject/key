/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;

import org.jspecify.annotations.NonNull;

public class ModularJavaDLStrategy extends AbstractFeatureStrategy {

    public static final Name NAME = new Name("Modular JavaDL Strategy");

    private final List<AbstractFeatureStrategy> strategies = new ArrayList<>();
    private final StrategyProperties strategyProperties;

    public ModularJavaDLStrategy(Proof proof, StrategyProperties strategyProperties) {
        super(proof);
        strategies.add(new JavaCardDLStrategy(proof, strategyProperties));
        strategies.add(new IntegerStrategy(proof, strategyProperties));
        this.strategyProperties = (StrategyProperties) strategyProperties.clone();
    }

    @Override
    protected RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
            MutableState mState) {
        return strategies.stream().map(s -> s.instantiateApp(app, pio, goal, mState)).reduce(
            longConst(0).computeCost(app, pio, goal, mState),
            RuleAppCost::add);
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return strategyProperties.getProperty(StrategyProperties.STOPMODE_OPTIONS_KEY)
                .equals(StrategyProperties.STOPMODE_NONCLOSE);
    }

    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        return strategies.stream().allMatch(s -> s.isApprovedApp(app, pio, goal));
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public <GOAL extends ProofGoal<@NonNull GOAL>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, GOAL goal, MutableState mState) {
        return strategies.stream().map(s -> s.computeCost(app, pos, goal, mState)).reduce(
            longConst(0).computeCost(app, pos, goal, mState),
            RuleAppCost::add);
    }
}
