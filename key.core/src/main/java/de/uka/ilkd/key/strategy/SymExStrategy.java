/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.strategy.feature.*;
import de.uka.ilkd.key.strategy.feature.findprefix.FindPrefixRestrictionFeature;
import de.uka.ilkd.key.strategy.termProjection.TermBuffer;
import de.uka.ilkd.key.strategy.termgenerator.SuperTermGenerator;

import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.IBuiltInRule;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.ComponentStrategy;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.feature.FindDepthFeature;
import org.key_project.prover.strategy.costbased.feature.RuleSetDispatchFeature;
import org.key_project.prover.strategy.costbased.feature.ScaleFeature;
import org.key_project.prover.strategy.costbased.feature.SumFeature;

import org.jspecify.annotations.NonNull;

/// Strategy for symbolic execution rules.
///
/// Do not create directly. Use [SymExStrategyFactory] instead.
public class SymExStrategy extends AbstractFeatureStrategy implements ComponentStrategy<Goal> {
    public static final Name NAME = new Name("SymExStrategy");

    private final FormulaTermFeatures ff;

    private final StrategyProperties strategyProperties;

    private final RuleSetDispatchFeature costComputationDispatcher;
    private final Feature costComputationF;
    private final RuleSetDispatchFeature instantiationDispatcher;
    private final Feature instantiationF;

    public SymExStrategy(Proof proof, StrategyProperties strategyProperties) {
        super(proof);

        this.strategyProperties = strategyProperties;
        var tf = new ArithTermFeatures(getServices().getTypeConverter().getIntegerLDT());
        ff = new FormulaTermFeatures(tf);

        costComputationDispatcher = setupCostComputationF();
        instantiationDispatcher = new RuleSetDispatchFeature();

        costComputationF = setupGlobalF(costComputationDispatcher);
        instantiationF = setupGlobalF(instantiationDispatcher);
    }

    @Override
    public boolean isResponsibleFor(RuleSet rs) {
        return costComputationDispatcher.get(rs) != null || instantiationDispatcher.get(rs) != null;
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
    public RuleSetDispatchFeature getDispatcher(StrategyAspect aspect) {
        return switch (aspect) {
            case StrategyAspect.Cost -> costComputationDispatcher;
            case StrategyAspect.Instantiation -> instantiationDispatcher;
            default -> null;
        };
    }


    private Feature setupGlobalF(Feature dispatcher) {
        final Feature methodSpecF;
        final String methProp =
            strategyProperties.getProperty(StrategyProperties.METHOD_OPTIONS_KEY);
        switch (methProp) {
            case StrategyProperties.METHOD_CONTRACT ->
                methodSpecF = methodSpecFeature(longConst(-20));
            case StrategyProperties.METHOD_EXPAND, StrategyProperties.METHOD_NONE -> methodSpecF =
                methodSpecFeature(inftyConst());
            default -> {
                methodSpecF = null;
                assert false;
            }
        }

        Feature loopInvF;
        final String loopProp = strategyProperties.getProperty(StrategyProperties.LOOP_OPTIONS_KEY);
        if (loopProp.equals(StrategyProperties.LOOP_INVARIANT)) {
            loopInvF = loopInvFeature(longConst(0));
        } else {
            loopInvF = loopInvFeature(inftyConst());
        }

        final Feature blockFeature;
        final Feature loopBlockFeature;
        final Feature loopBlockApplyHeadFeature;
        final String blockProperty =
            strategyProperties.getProperty(StrategyProperties.BLOCK_OPTIONS_KEY);
        if (blockProperty.equals(StrategyProperties.BLOCK_CONTRACT_INTERNAL)) {
            blockFeature = blockContractInternalFeature(longConst(Long.MIN_VALUE));
            loopBlockFeature = loopContractInternalFeature(longConst(Long.MIN_VALUE));
            loopBlockApplyHeadFeature = loopContractApplyHead(longConst(Long.MIN_VALUE));
        } else if (blockProperty.equals(StrategyProperties.BLOCK_CONTRACT_EXTERNAL)) {
            blockFeature = blockContractExternalFeature(longConst(Long.MIN_VALUE));
            loopBlockFeature =
                SumFeature.createSum(loopContractExternalFeature(longConst(Long.MIN_VALUE)),
                    loopContractInternalFeature(longConst(42)));
            loopBlockApplyHeadFeature = loopContractApplyHead(longConst(Long.MIN_VALUE));
        } else {
            blockFeature = blockContractInternalFeature(inftyConst());
            loopBlockFeature = loopContractExternalFeature(inftyConst());
            loopBlockApplyHeadFeature = loopContractApplyHead(inftyConst());
        }

        final Feature mergeRuleF;
        final String mpsProperty =
            strategyProperties.getProperty(StrategyProperties.MPS_OPTIONS_KEY);
        if (mpsProperty.equals(StrategyProperties.MPS_MERGE)) {
            mergeRuleF = mergeRuleFeature(longConst(-4000));
        } else {
            mergeRuleF = mergeRuleFeature(inftyConst());
        }
        return SumFeature.createSum(mergeRuleF, methodSpecF, loopInvF, blockFeature,
            loopBlockFeature, loopBlockApplyHeadFeature, dispatcher);
    }

    private RuleSetDispatchFeature setupCostComputationF() {
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

        bindRuleSet(d, "simplify_java", -4500);

        bindRuleSet(d, "executeIntegerAssignment", -100);
        bindRuleSet(d, "executeDoubleAssignment", -100);

        final Feature findDepthFeature =
            FindDepthFeature.getInstance();
        bindRuleSet(d, "concrete_java",
            add(longConst(-11000),
                ScaleFeature.createScaled(findDepthFeature, 10.0)));

        // taclets for special invariant handling
        bindRuleSet(d, "loopInvariant", -20000);

        boolean useLoopExpand = strategyProperties.getProperty(StrategyProperties.LOOP_OPTIONS_KEY)
                .equals(StrategyProperties.LOOP_EXPAND);
        boolean useLoopInvTaclets =
            strategyProperties.getProperty(StrategyProperties.LOOP_OPTIONS_KEY)
                    .equals(StrategyProperties.LOOP_SCOPE_INV_TACLET);
        boolean useLoopScopeExpand =
            strategyProperties.getProperty(StrategyProperties.LOOP_OPTIONS_KEY)
                    .equals(StrategyProperties.LOOP_SCOPE_EXPAND);

        bindRuleSet(d, "loop_expand", useLoopExpand ? longConst(0) : inftyConst());
        bindRuleSet(d, "loop_scope_inv_taclet", useLoopInvTaclets ? longConst(0) : inftyConst());
        bindRuleSet(d, "loop_scope_expand", useLoopScopeExpand ? longConst(1000) : inftyConst());


        final String methProp =
            strategyProperties.getProperty(StrategyProperties.METHOD_OPTIONS_KEY);
        switch (methProp) {
            case StrategyProperties.METHOD_CONTRACT ->
                /*
                 * If method treatment by contracts is chosen, this does not mean that method
                 * expansion
                 * is disabled. The original cost was 200 and is now increased to 2000 in order to
                 * repress method expansion stronger when method treatment by contracts is chosen.
                 */
                bindRuleSet(d, "method_expand", longConst(2000));
            case StrategyProperties.METHOD_EXPAND ->
                bindRuleSet(d, "method_expand", longConst(100));
            case StrategyProperties.METHOD_NONE -> bindRuleSet(d, "method_expand", inftyConst());
            default -> throw new RuntimeException("Unexpected strategy property " + methProp);
        }

        final String mpsProp = strategyProperties.getProperty(StrategyProperties.MPS_OPTIONS_KEY);
        switch (mpsProp) {
            case StrategyProperties.MPS_MERGE ->
                /*
                 * For this case, we use a special feature, since deleting merge points should only
                 * be
                 * done after a merge rule application.
                 */
                bindRuleSet(d, "merge_point", DeleteMergePointRuleFeature.INSTANCE);
            case StrategyProperties.MPS_SKIP -> bindRuleSet(d, "merge_point", longConst(-5000));
            case StrategyProperties.MPS_NONE -> bindRuleSet(d, "merge_point", inftyConst());
            default -> throw new RuntimeException("Unexpected strategy property " + mpsProp);
        }

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
    public RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
            MutableState mState) {
        return instantiationF.computeCost(app, pio, goal, mState);
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return false;
    }

    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        return true;
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public <GOAL extends ProofGoal<@NonNull GOAL>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, GOAL goal, MutableState mState) {
        return costComputationF.computeCost(app, pos, goal, mState);
    }

    @Override
    public boolean isResponsibleFor(IBuiltInRule rule) {
        return rule instanceof WhileInvariantRule || rule instanceof LoopScopeInvariantRule
                || rule instanceof BlockContractInternalRule
                || rule instanceof BlockContractExternalRule
                || rule instanceof LoopContractInternalRule
                || rule instanceof LoopContractExternalRule
                || rule instanceof LoopApplyHeadRule || rule instanceof UseOperationContractRule
                || rule instanceof MergeRule;
    }
}
