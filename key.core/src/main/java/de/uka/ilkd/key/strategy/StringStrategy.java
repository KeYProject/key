/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.ldt.BooleanLDT;
import de.uka.ilkd.key.ldt.CharListLDT;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.feature.*;
import de.uka.ilkd.key.strategy.termProjection.*;

import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.feature.SumFeature;
import org.key_project.prover.strategy.costbased.termfeature.OperatorClassTF;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

import org.jspecify.annotations.NonNull;

public class StringStrategy extends AbstractFeatureStrategy {
    public static final Name NAME = new Name("String Strategy");

    /// The features defining the three phases: cost computation, approval,
    /// additionalInstanceCreationAndEvaluation
    private final RuleSetDispatchFeature costComputationDispatcher;

    /// Useful [TermFeature] collections
    private final ArithTermFeatures tf;
    private final FormulaTermFeatures ff;

    private final boolean stopAtFirstNonCloseableGoal;

    public StringStrategy(Proof proof, StrategyProperties strategyProperties) {
        super(proof);
        this.tf = new ArithTermFeatures(proof.getServices().getTypeConverter().getIntegerLDT());
        this.ff = new FormulaTermFeatures(this.tf);

        costComputationDispatcher = setupCostComputationF();

        stopAtFirstNonCloseableGoal =
            strategyProperties.getProperty(StrategyProperties.STOPMODE_OPTIONS_KEY)
                    .equals(StrategyProperties.STOPMODE_NONCLOSE);
    }

    @Override
    public boolean isResponsibleFor(RuleSet rs) {
        return costComputationDispatcher.get(rs) != null;
    }

    private RuleSetDispatchFeature setupCostComputationF() {
        final RuleSetDispatchFeature d = new RuleSetDispatchFeature();
        setUpStringNormalisation(d);
        return d;
    }

    private void setUpStringNormalisation(RuleSetDispatchFeature d) {
        // translates an integer into its string representation
        bindRuleSet(d, "integerToString", -10000);

        // do not convert char to int when inside a string function
        // feature used to recognize if one is inside a string literal
        final SeqLDT seqLDT = getServices().getTypeConverter().getSeqLDT();
        final CharListLDT charListLDT = getServices().getTypeConverter().getCharListLDT();
        final BooleanLDT booleanLDT = getServices().getTypeConverter().getBooleanLDT();


        final TermFeature keepChar =
            or(op(seqLDT.getSeqSingleton()), or(op(charListLDT.getClIndexOfChar()),
                or(op(charListLDT.getClReplace()), op(charListLDT.getClLastIndexOfChar()))));

        bindRuleSet(d, "charLiteral_to_intLiteral",
            ifZero(isBelow(keepChar), inftyConst(), longConst(-100)));

        // establish normalform

        // tf below only for test
        final TermFeature anyLiteral = or(tf.charLiteral,
            or(tf.literal, op(booleanLDT.getFalseConst()), op(booleanLDT.getTrueConst())));

        final TermFeature seqLiteral = rec(anyLiteral, or(op(seqLDT.getSeqConcat()),
            or(op(seqLDT.getSeqSingleton()), or(anyLiteral, inftyTermConst()))));

        Feature belowModOpPenality = ifZero(isBelow(ff.modalOperator), longConst(500));

        bindRuleSet(d, "defOpsSeqEquality",
            add(NonDuplicateAppModPositionFeature.INSTANCE,
                ifZero(add(applyTF("left", seqLiteral), applyTF("right", seqLiteral)),
                    longConst(1000), inftyConst()),
                belowModOpPenality));

        bindRuleSet(d, "defOpsConcat",
            add(NonDuplicateAppModPositionFeature.INSTANCE,
                ifZero(
                    or(applyTF("leftStr", not(seqLiteral)), applyTF("rightStr", not(seqLiteral))),
                    longConst(1000)
                // concat is often introduced for construction purposes,
                // we do not want to use its definition right at the
                // beginning
                ), belowModOpPenality));

        bindRuleSet(d, "stringsSimplify", longConst(-5000));

        final TermFeature charOrIntLiteral = or(tf.charLiteral, tf.literal,
            or(add(OperatorClassTF.create(SortDependingFunction.class), // XXX:
                // was CastFunctionSymbol.class
                sub(tf.literal)), inftyTermConst()));

        bindRuleSet(d, "defOpsReplaceInline",
            ifZero(add(applyTF("str", seqLiteral), applyTF("searchChar", charOrIntLiteral),
                applyTF("replChar", charOrIntLiteral)), longConst(-2500), inftyConst()));

        bindRuleSet(d, "defOpsReplace", add(NonDuplicateAppModPositionFeature.INSTANCE,
            ifZero(or(applyTF("str", not(seqLiteral)), applyTF("searchChar", not(charOrIntLiteral)),
                applyTF("replChar", not(charOrIntLiteral))), longConst(500), inftyConst()),
            belowModOpPenality));

        bindRuleSet(d, "stringsReduceSubstring",
            add(NonDuplicateAppModPositionFeature.INSTANCE, longConst(100)));

        bindRuleSet(d, "defOpsStartsEndsWith", longConst(250));

        bindRuleSet(d, "stringsConcatNotBothLiterals",
            ifZero(MatchedAssumesFeature.INSTANCE, ifZero(
                add(applyTF(instOf("leftStr"), seqLiteral),
                    applyTF(instOf("rightStr"), seqLiteral)),
                inftyConst()), inftyConst()));

        bindRuleSet(d, "stringsReduceConcat", longConst(100));

        bindRuleSet(d, "stringsReduceOrMoveOutsideConcat",
            ifZero(NonDuplicateAppModPositionFeature.INSTANCE, longConst(800), inftyConst()));

        bindRuleSet(d, "stringsMoveReplaceInside",
            ifZero(NonDuplicateAppModPositionFeature.INSTANCE, longConst(400), inftyConst()));


        bindRuleSet(d, "stringsExpandDefNormalOp", longConst(500));

        bindRuleSet(d, "stringsContainsDefInline", SumFeature
                .createSum(EqNonDuplicateAppFeature.INSTANCE, longConst(1000)));
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return stopAtFirstNonCloseableGoal;
    }

    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        return NonDuplicateAppFeature.INSTANCE.computeCost(app, pio, goal,
            new MutableState()) != TopRuleAppCost.INSTANCE;
    }

    @Override
    protected RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
            MutableState mState) {
        return longConst(0).computeCost(app, pio, goal, mState);
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, Goal goal, MutableState mState) {
        return this.costComputationDispatcher.computeCost(app, pos, goal, mState);
    }

    @Override
    protected RuleSetDispatchFeature getCostDispatcher() {
        return costComputationDispatcher;
    }
}
