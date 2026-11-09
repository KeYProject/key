/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.strategy.feature.NonDuplicateAppModPositionFeature;
import de.uka.ilkd.key.strategy.feature.RuleSetDispatchFeature;
import de.uka.ilkd.key.strategy.feature.SeqEqualLengthFeature;
import de.uka.ilkd.key.strategy.feature.SeqSameBasesFeature;
import de.uka.ilkd.key.strategy.feature.findprefix.FindPrefixRestrictionFeature;
import de.uka.ilkd.key.strategy.feature.findprefix.FindPrefixRestrictionFeature.PrefixChecker;
import de.uka.ilkd.key.strategy.termProjection.FocusProjection;

import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.CostBand;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.strategy.SeqCost.*;

/// Strategy for reasoning about sequences
public class SeqStrategy extends AbstractFeatureStrategy implements ComponentStrategy {
    public static final Name NAME = new Name("Sequence Strategy");

    private final SeqTermFeatures tf;
    private final RuleSetDispatchFeature costDispatcher;
    private final RuleSetDispatchFeature approvalDispatcher;
    private final boolean stopAtFirstNonCloseableGoal;

    public SeqStrategy(Proof proof, StrategyProperties strategyProperties) {
        super(proof);
        final TypeConverter types = getServices().getTypeConverter();
        tf = new SeqTermFeatures(types.getSeqLDT(), types.getPSeqLDT(), types.getIntegerLDT(),
            types.getBooleanLDT());
        costDispatcher = setupCostDispatcher();
        approvalDispatcher = setupApprovalDispatcher();
        stopAtFirstNonCloseableGoal =
            strategyProperties.getProperty(StrategyProperties.STOPMODE_OPTIONS_KEY)
                    .equals(StrategyProperties.STOPMODE_NONCLOSE);
    }

    private RuleSetDispatchFeature setupCostDispatcher() {
        final RuleSetDispatchFeature d = new RuleSetDispatchFeature();
        final ProjectionToTerm<Goal> focus = FocusProjection.INSTANCE;

        // Equality reasoning on sequences: an equation is replaced by its elementwise definition
        // late, to allow for normalisation, simplification and equation based reasoning before
        // defaulting to quantification.
        final Feature eqBetweenConstructors =
            add(applyTF("s", tf.constructor), applyTF("s2", tf.constructor));

        // Do not add length information to antecedent for sequences for which equal length can
        // be derived
        // Assume a situation like
        // `seqConcat(s1, s2) = seqConcat(s1, s3), seqLen(s2) = seqLen(s3) ==> ... `
        // The rule would add
        // `seqConcat(s1, s2) = seqConcat(s1, s3), seqLen(s2) = seqLen(s3),
        // seqLen(seqConcat(s1, s2)) = seqLen(seqConcat(s1, s3)) ==> ...`
        // which would then simply be rewritten to the original sequent adding additional work with
        // no gain
        bindRuleSet(d, "seqLenOfEquality", add(eqBetweenConstructors,
            not(SeqEqualLengthFeature.create(instOf("s"), instOf("s2"), tf)),
            NonDuplicateAppModPositionFeature.INSTANCE, longConst(DEFER_SLIGHTLY)));

        // as the rule for `get(seqDef(..)..)` might split the expansion of the sequence should be
        // done first
        final Feature getOnDefinitionalSeq = or(applyTF(sub(focus, 0), tf.defOverGets),
            applyTF(sub(focus, 1), tf.defOverGets));
        bindRuleSet(d, "seqEqExpandAntec",
            add(eqBetweenConstructors, NonDuplicateAppModPositionFeature.INSTANCE,
                ifZero(getOnDefinitionalSeq, longConst(EXPAND_BEFORE_SEQDEF_SPLIT),
                    CostBand.DEFER.cost())));

        // if the sequence `s` of a `seqGet(s,i)` on one side of an equation is not concrete
        // `seqRead`-rules can be applied with low costs, otherwise
        // the general `seqRead` rules should stand back and other rules like
        // `getOfSeqSingletonConcrete` should be given a chance to be used first
        bindRuleSet(d, "seqRead", ifZero(isReadFromSymbolicSequenceInEquation(),
            CostBand.SIMPLIFY.cost(), CostBand.ENLARGE.cost()));

        // seqDefOfStore should be applied late to allow for simplifications first
        // as it enlarges the term significantly
        bindRuleSet(d, "seqDefStore", CostBand.DEFER_STRONG.cost());

        setupSequencePermutationStrategy(d);

        return d;
    }

    private void setupSequencePermutationStrategy(RuleSetDispatchFeature d) {
        // a bit more general as the name indicates
        final Feature focusInSuccedent =
            new FindPrefixRestrictionFeature(PrefixChecker.SUCC_POLARITY);

        // the rule `seqPermCount` replaces `seqPerm(s1,s2)` by a quantified formula that
        // expresses that the number of each element is equal in `s1` and `s2`.
        // This introduces quantification and is therefore expensive.
        // Hence, it should be done late if both sequences are built from the same base sequences
        // (as they usually share then some of the element numbers).
        // Otherwise, it should only be used as a last resort if nothing else can be done anymore.
        bindRuleSet(d, "seqPermCount", add(focusInSuccedent, notBelowQuantifier(),
            ifZero(SeqSameBasesFeature.create(tf), CostBand.DEFER_STRONG.cost(),
                CostBand.LAST_RESORT.cost())));

        bindRuleSet(d, "seqPermCountAntec",
            add(NonDuplicateAppModPositionFeature.INSTANCE, longConst(AXIOM_LIKE)));

        bindRuleSet(d, "seqCountSimp", CostBand.SIMPLIFY.cost());

        bindRuleSet(d, "seqPermTransitivity",
            add(NonDuplicateAppModPositionFeature.INSTANCE, longConst(AXIOM_LIKE)));

        bindRuleSet(d, "seqNPermProperties", add(NonDuplicateAppModPositionFeature.INSTANCE,
            notBelowQuantifier(), longConst(AXIOM_LIKE)));
    }

    /// The returned feature checks that the focus term is a `seqGet` that appears as top level
    /// on one side of an equation and the sequence it queries is not concrete.
    private Feature isReadFromSymbolicSequenceInEquation() {
        return add(applyTF(sub(FocusProjection.INSTANCE, 0), not(tf.concreteSeq)),
            or(directlyBelowSymbolAtIndex(Equality.EQUALS, 0),
                directlyBelowSymbolAtIndex(Equality.EQUALS, 1)));
    }

    private RuleSetDispatchFeature setupApprovalDispatcher() {
        final RuleSetDispatchFeature d = new RuleSetDispatchFeature();
        bindRuleSet(d, "seqPermTransitivity", NonDuplicateAppModPositionFeature.INSTANCE);
        bindRuleSet(d, "seqLenOfEquality", NonDuplicateAppModPositionFeature.INSTANCE);
        bindRuleSet(d, "seqEqExpandAntec", NonDuplicateAppModPositionFeature.INSTANCE);
        bindRuleSet(d, "seqNPermProperties", NonDuplicateAppModPositionFeature.INSTANCE);
        bindRuleSet(d, "seqPermCountAntec", NonDuplicateAppModPositionFeature.INSTANCE);
        return d;
    }

    @Override
    public boolean isResponsibleFor(RuleSet rs) {
        return costDispatcher.get(rs) != null;
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return stopAtFirstNonCloseableGoal;
    }

    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        return approvalDispatcher.computeCost(app, pio, goal,
            new MutableState()) != TopRuleAppCost.INSTANCE;
    }

    @Override
    public RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
            MutableState mState) {
        return longConst(0).computeCost(app, pio, goal, mState);
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public <GOAL extends ProofGoal<@NonNull GOAL>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, GOAL goal, MutableState mState) {
        return costDispatcher.computeCost(app, pos, goal, mState);
    }

    @Override
    public Set<RuleSet> getResponsibilities(StrategyAspect aspect) {
        var set = new HashSet<RuleSet>();
        RuleSetDispatchFeature dispatcher = getDispatcher(aspect);
        if (dispatcher != null) {
            set.addAll(dispatcher.ruleSets());
        }
        return set;
    }

    @Override
    public @Nullable RuleSetDispatchFeature getDispatcher(StrategyAspect aspect) {
        return switch (aspect) {
            case Cost -> costDispatcher;
            case Approval -> approvalDispatcher;
            case Instantiation -> null;
        };
    }

    @Override
    public boolean isResponsibleFor(BuiltInRule rule) {
        return false;
    }
}
