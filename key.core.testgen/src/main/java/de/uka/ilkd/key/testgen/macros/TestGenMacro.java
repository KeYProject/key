/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.macros;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.FilterStrategy;
import de.uka.ilkd.key.macros.ModalityCache;
import de.uka.ilkd.key.macros.StrategyProofMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.testgen.settings.TestGenerationSettings;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.feature.MutableState;
import de.uka.ilkd.key.testgen.settings.TestGenerationSettings;

import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.Rule;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;

import org.jspecify.annotations.NonNull;

public class TestGenMacro extends StrategyProofMacro {
    @Override
    protected Strategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
        return new TestGenStrategy(proof.getActiveStrategy());
    }

    @Override
    public String getDescription() {
        return "Finish symbolic execution but restrict loop unwinding.";
    }

    @Override
    public String getName() {
        return "TestGen (finite loop unwinding)";
    }

    @Override
    public String getCategory() {
        return null;
    }


}


/**
 * The Class FilterAppManager is a special strategy assigning to any rule infinite costs if the goal
 * has no modality
 */
class TestGenStrategy extends FilterStrategy {
    private static final Name NAME = new Name(TestGenStrategy.class.getSimpleName());
    private static final Set<String> unwindRules;
    private static final int UNWIND_COST = 1000;
    private final int limit;
    /** the modality cache used by this strategy */
    private final ModalityCache modalityCache = new ModalityCache();
    static {
        unwindRules = new HashSet<>();
        unwindRules.add("loopUnwind");
        unwindRules.add("doWhileUnwind");
        unwindRules.add("methodCall");
        unwindRules.add("methodCallWithAssignment");
        unwindRules.add("staticMethodCall");
        unwindRules.add("staticMethodCallWithAssignment");
    }

    private static boolean isUnwindRule(Rule rule) {
        if (rule == null) {
            return false;
        }
        final String name = rule.name().toString();
        return unwindRules.contains(name);
    }

    public TestGenStrategy(Strategy delegate) {
        super(delegate);
        limit = TestGenerationSettings.getInstance().getMaximalUnwinds();
    }

    @Override
    public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pio,
            Goal goal,
            MutableState mState) {
        if (isUnwindRule(app.rule())) {
            return NumberRuleAppCost.create(UNWIND_COST);
        }
        return super.computeCost(app, pio, goal, mState);
    }

    private int computeUnwindRules(Goal goal) {
        int totalUnwinds = 0;
        Node node = goal.node();
        while (!node.root()) {
            final RuleApp app = node.getAppliedRuleApp();
            if (app != null) {
                final Rule rule = app.rule();
                if (isUnwindRule(rule)) {
                    ++totalUnwinds;
                }
            }
            node = node.parent();
        }
        return totalUnwinds;
    }

    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        if (!modalityCache.hasModality(goal.node().sequent())) {
            return false;
        }
        if (isUnwindRule(app.rule())) {
            final int noUnwindRules = computeUnwindRules(goal);
            return noUnwindRules < limit;
        }
        return super.isApprovedApp(app, pio, goal);
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return false;
    }
}
