/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.feature.DiffFindAndIfFeature;
import de.uka.ilkd.key.strategy.feature.MatchedAssumesFeature;
import de.uka.ilkd.key.strategy.feature.RuleSetDispatchFeature;
import de.uka.ilkd.key.strategy.feature.ThrownExceptionFeature;
import de.uka.ilkd.key.strategy.feature.findprefix.FindPrefixRestrictionFeature;
import de.uka.ilkd.key.strategy.termProjection.TermBuffer;
import de.uka.ilkd.key.strategy.termgenerator.SuperTermGenerator;

import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.feature.SumFeature;

import org.jspecify.annotations.NonNull;

/// Strategy for symbolic execution rules
public class SymExStrategy extends AbstractFeatureStrategy {
    public static final Name NAME = new Name("SymExStrategy");

    private final FormulaTermFeatures ff;

    public SymExStrategy(Proof proof) {
        super(proof);

        var tf = new ArithTermFeatures(getServices().getTypeConverter().getIntegerLDT());
        ff = new FormulaTermFeatures(tf);
    }

    private RuleSetDispatchFeature setUpCostComputationF() {
        final RuleSetDispatchFeature d = new RuleSetDispatchFeature();
        boolean programsToRight = true; // XXX

        final String[] exceptionsWithPenalty = { "java.lang.NullPointerException",
            "java.lang.ArrayIndexOutOfBoundsException", "java.lang.ArrayStoreException",
            "java.lang.ClassCastException" };

        bindRuleSet(d, "simplify_prog",
            ifZero(ThrownExceptionFeature.create(exceptionsWithPenalty, getServices()),
                longConst(500),
                ifZero(isBelow(add(ff.forF, not(ff.atom))), longConst(200), longConst(-100))));

        bindRuleSet(d, "simplify_prog_subset", longConst(-4000));

        bindRuleSet(d, "simplify_expression", -100);

        // simplify
        // concrete
        // method_expand
        // merge_point

        bindRuleSet(d, "modal_tautology", longConst(-10000));

        if (programsToRight) {
            bindRuleSet(d, "boxDiamondConv",
                SumFeature.createSum(
                    new FindPrefixRestrictionFeature(
                        FindPrefixRestrictionFeature.PositionModifier.ALLOW_UPDATE_AS_PARENT,
                        FindPrefixRestrictionFeature.PrefixChecker.ANTEC_POLARITY),
                    longConst(-1000)));
        } else {
            bindRuleSet(d, "boxDiamondConv", inftyConst());
        }

        bindRuleSet(d, "confluence_restricted",
            ifZero(MatchedAssumesFeature.INSTANCE, DiffFindAndIfFeature.INSTANCE));

        final TermBuffer superFor = new TermBuffer();
        bindRuleSet(d, "split_if",
            add(sum(superFor, SuperTermGenerator.upwards(any(), getServices()),
                applyTF(superFor, not(ff.program))), longConst(50)));

        return d;
    }

    @Override
    protected RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
            MutableState mState) {
        return null;
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return false;
    }

    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        return false;
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public <GOAL extends ProofGoal<@NonNull GOAL>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, GOAL goal, MutableState mState) {
        return null;
    }
}
