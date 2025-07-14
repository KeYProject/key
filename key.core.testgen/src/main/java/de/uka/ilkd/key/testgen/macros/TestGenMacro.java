/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.macros;

import java.util.Set;

import de.uka.ilkd.key.macros.FilterStrategy;
import de.uka.ilkd.key.macros.ModalityCache;
import de.uka.ilkd.key.macros.StrategyProofMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.testgen.TestGenerationSettings;

import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.Rule;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public class TestGenMacro extends StrategyProofMacro {
    public final int unwindLimit;

    public TestGenMacro() {
        this(TestGenerationSettings.getInstance().getMaximalUnwinds());
    }

    public TestGenMacro(int unwindLimit) {
        this.unwindLimit = unwindLimit;
    }

    @Override
    protected Strategy<Goal> createStrategy(Proof proof, PosInOccurrence posInOcc) {
        return new TestGenStrategy(proof.getActiveStrategy(), unwindLimit);
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
    @Nullable
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
    private static final Set<String> unwindRules = Set.of(
        "loopUnwind", "doWhileUnwind", "methodCall", "methodCallWithAssignment",
        "staticMethodCall", "staticMethodCallWithAssignment");
    private static final int UNWIND_COST = 1000;
    private final int limit;

    /**
     * the modality cache used by this strategy
     */
    private final ModalityCache modalityCache = new ModalityCache();

    private static boolean isUnwindRule(org.key_project.prover.rules.Rule rule) {
        if (rule == null) {
            return false;
        }
        final String name = rule.name().toString();
        return unwindRules.contains(name);
    }

    public TestGenStrategy(Strategy<Goal> delegate, int unwindLimit) {
        super(delegate);
        limit = unwindLimit;
    }

    @Override
    public <G extends ProofGoal<@NonNull G>> RuleAppCost computeCost(
            RuleApp app, PosInOccurrence pio, G goal, MutableState mState) {
        if (isUnwindRule(app.rule())) {
            return NumberRuleAppCost.create(UNWIND_COST);
        }
        return super.computeCost(app, pio, goal, mState);
    }

    private int computeUnwindRules(Goal goal) {
        int totalUnwinds = 0;
        Node node = goal.node();
        while (node != null && !node.root()) {
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
