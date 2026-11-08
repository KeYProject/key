/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy;

import java.util.Objects;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;

import org.key_project.prover.indexing.FormulaTag;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


/**
 * Instances of this class are immutable
 */
@NullMarked
public class BuiltInRuleAppContainer extends RuleAppContainer {

    /**
     * The position of the rule app in two different representations: <code>positionTag</code>
     * denotes the concerned formula and survives modifications of the sequent and of parts of the
     * formula, and <code>applicationPosition</code> is the original position for which the rule app
     * was created
     */
    private final @Nullable FormulaTag positionTag;
    private final @Nullable PosInOccurrence applicationPosition;

    private final IBuiltInRuleApp bir;



    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    private BuiltInRuleAppContainer(IBuiltInRuleApp bir,
            @Nullable PosInOccurrence pio, RuleAppCost cost,
            Goal goal) {
        super(bir, cost);
        applicationPosition = pio;
        positionTag = pio == null ? null : goal.getFormulaTagManager().getTagForPos(pio.topLevel());
        this.bir = bir;
        assert !(pio != null && positionTag == null) : "Formula " + pio + " does not exist";
    }



    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    /**
     * @return true iff the stored rule app is applicable for the given sequent, i.e. if the bound
     *         position does still exist (if-formulas are not considered)
     */
    private boolean isStillApplicable(Goal goal) {
        if (applicationPosition == null) {
            return bir.rule().isApplicable(goal, null);
        } else {
            // the constructor guarantees a non-null position tag for every non-null application
            // position; declaring the parameter non-null, the tag manager look-up tolerates null
            // (it would answer "no such formula"), which main relies on only for the impossibility
            // rejected by the constructor assertion
            @SuppressWarnings("NullAway") // positionTag is non-null when applicationPosition is not
            final PosInOccurrence topPos =
                goal.getFormulaTagManager().getPosForTag(positionTag);
            if (topPos == null) {
                // the formula does not exist anymore, bail out
                return false;
            } else {
                return topPos.sequentFormula().equals(applicationPosition.sequentFormula());
            }
        }
    }


    /**
     * Copied from FindTaclet.
     */
    private PosInOccurrence getPosInOccurrence(Goal p_goal) {
        final PosInOccurrence topPos = Objects.requireNonNull(
            p_goal.getFormulaTagManager().getPosForTag(
                Objects.requireNonNull(positionTag, "no position tag for the formula")),
            "the formula for the stored position does not exist any more");

        return Objects.requireNonNull(applicationPosition, "no application position")
                .replaceSequentFormula(topPos.sequentFormula());
    }



    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    /**
     * Create container for RuleApp.
     *
     * @return container for the currently applicable BuiltInRuleApp, the cost may be an instance of
     *         <code>TopRuleAppCost</code>.
     */
    static RuleAppContainer createAppContainer(IBuiltInRuleApp bir,
            @Nullable PosInOccurrence pio,
            Goal goal) {
        // a null position (a rule app without a find section) is legitimately handed to the
        // strategy's cost computation, which tolerates it; the parameter is still declared @NonNull
        // there.
        @SuppressWarnings("NullAway")
        final RuleAppCost cost =
            withAge(goal.getGoalStrategy().computeCost(bir, pio, goal), goal);
        return new BuiltInRuleAppContainer(bir, pio, cost, goal);
    }

    /**
     * Create container for RuleApp.
     *
     * @return container for the currently applicable BuiltInRuleApp, the cost may be an instance of
     *         <code>TopRuleAppCost</code>.
     */
    static ImmutableList<RuleAppContainer> createInitialAppContainers(
            ImmutableList<IBuiltInRuleApp> birs, @Nullable PosInOccurrence pio,
            Goal goal) {
        ImmutableList<RuleAppContainer> result = ImmutableList.nil();

        for (IBuiltInRuleApp bir : birs) {
            result = result.prepend(createAppContainer(bir, pio, goal));
        }

        return result;
    }



    @Override
    public ImmutableList<RuleAppContainer> createFurtherApps(Goal goal) {
        if (!isStillApplicable(goal)) {
            return ImmutableList.nil();
        }

        final PosInOccurrence pio = getPosInOccurrence(goal);

        RuleAppContainer container = createAppContainer(bir, pio, goal);
        if (container.getCost() instanceof TopRuleAppCost) {
            return ImmutableList.nil();
        }
        return ImmutableList.<RuleAppContainer>singleton(container);
    }


    @Override
    public @Nullable RuleApp completeRuleApp(Goal goal) {
        if (!isStillApplicable(goal)) {
            return null;
        }

        final PosInOccurrence pio = getPosInOccurrence(goal);
        if (!goal.getGoalStrategy().isApprovedApp(bir, pio, goal)) {
            return null;
        }

        final BuiltInRule rule = bir.rule();
        IBuiltInRuleApp app = rule.createApp(pio, goal.proof().getServices());

        if (!app.complete()) {
            app = app.setAssumesInsts(bir.assumesInsts());
            // TODO: check for force ?
            final boolean force = true;
            app = force ? app.forceInstantiate(goal) : app.tryToInstantiate(goal);
        }

        return app.complete() ? app : null;
    }
}
