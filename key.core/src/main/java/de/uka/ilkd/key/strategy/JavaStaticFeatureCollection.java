/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.LexPathOrdering;
import de.uka.ilkd.key.logic.equality.RenamingTermProperty;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.ParametricFunctionDecl;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.strategy.feature.*;
import de.uka.ilkd.key.strategy.quantifierHeuristics.LiteralsSmallerThanFeature;
import de.uka.ilkd.key.strategy.termProjection.*;
import de.uka.ilkd.key.strategy.termfeature.ParametricFunctionBaseTermFeature;

import org.key_project.logic.TermOrdering;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.prover.proof.rulefilter.RuleFilter;
import org.key_project.prover.strategy.costbased.feature.*;
import org.key_project.prover.strategy.costbased.termProjection.FocusProjection;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;
import org.key_project.prover.strategy.costbased.termProjection.TermBuffer;
import org.key_project.prover.strategy.costbased.termfeature.*;

/**
 * Collection of strategy features that can be accessed statically. This class is essentially a
 * collection of constructors for various features.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public abstract class JavaStaticFeatureCollection
        extends org.key_project.prover.strategy.StaticFeatureCollection {

    public static TermOrdering createTermOrdering() {
        return new LexPathOrdering();
    }

    protected static Feature loopInvFeature(Feature costStdInv) {
        // NOTE (DS, 2019-04-10): This feature also deactivates the built-in loop
        // scope invariant rule (always!) since we use the taclets now.
        final RuleFilter filterLoopInv = (r) -> r instanceof WhileInvariantRule;
        final RuleFilter filterLoopScopeInv = (r) -> r instanceof LoopScopeInvariantRule;

        return ConditionalFeature.createConditional(filterLoopInv, costStdInv,
            ConditionalFeature.createConditional(filterLoopScopeInv, inftyConst()));
    }

    /**
     * @param cost The specified cost.
     * @return a feature for {@link BlockContractInternalRule} with the specified cost.
     */
    protected static Feature blockContractInternalFeature(Feature cost) {
        RuleFilter filter = (p) -> p instanceof BlockContractInternalRule;
        return ConditionalFeature.createConditional(filter, cost);
    }

    /**
     * @param cost The specified cost.
     * @return a feature for {@link BlockContractExternalRule} with the specified cost.
     */
    protected static Feature blockContractExternalFeature(Feature cost) {
        RuleFilter filter = (r) -> r instanceof BlockContractExternalRule;
        return ConditionalFeature.createConditional(filter, cost);
    }

    /**
     * @param cost The specified cost.
     * @return a feature for {@link LoopContractInternalRule} with the specified cost.
     */
    protected static Feature loopContractInternalFeature(Feature cost) {
        RuleFilter filter = (r) -> r instanceof LoopContractInternalRule;
        return ConditionalFeature.createConditional(filter, cost);
    }

    /**
     * @param cost The specified cost.
     * @return a feature for {@link LoopContractExternalRule} with the specified cost.
     */
    protected static Feature loopContractExternalFeature(Feature cost) {
        RuleFilter filter = (r) -> r instanceof LoopContractExternalRule;
        return ConditionalFeature.createConditional(filter, cost);
    }

    /**
     * @param cost The specified cost.
     * @return a feature for {@link LoopApplyHeadRule} with the specified cost.
     */
    protected static Feature loopContractApplyHead(Feature cost) {
        RuleFilter filter = (r) -> r instanceof LoopApplyHeadRule;
        return ConditionalFeature.createConditional(filter, cost);
    }

    protected static Feature methodSpecFeature(Feature cost) {
        RuleFilter filter = (r) -> r instanceof UseOperationContractRule;
        return ConditionalFeature.createConditional(filter, cost);
    }

    protected static Feature querySpecFeature(Feature cost) {
        RuleFilter filter = (r) -> r instanceof QueryExpand;
        return ConditionalFeature.createConditional(filter, cost);
    }

    protected static Feature mergeRuleFeature(Feature cost) {
        RuleFilter filter = (r) -> r instanceof MergeRule;
        return ConditionalFeature.createConditional(filter,
            SumFeature.createSum(cost, MergeRuleFeature.INSTANCE));
    }

    protected static Feature sequentContainsNoPrograms() {
        return not(SeqContainsExecutableCodeFeature.PROGRAMS);
    }

    protected static Feature countOccurrences(ProjectionToTerm cutFormula) {
        return CountOccurrencesFeature.create(cutFormula,
            RenamingTermProperty.RENAMING_TERM_PROPERTY);
    }

    protected static Feature termSmallerThan(String smaller, String bigger) {
        return TermSmallerThanFeature.create(instOf(smaller), instOf(bigger), createTermOrdering());
    }

    protected static Feature monSmallerThan(String smaller, String bigger,
            IntegerLDT numbers) {
        return MonomialsSmallerThanFeature.create(instOf(smaller), instOf(bigger),
            createTermOrdering(), numbers);
    }

    protected static Feature atomSmallerThan(String smaller, String bigger,
            IntegerLDT numbers) {
        return AtomsSmallerThanFeature.create(instOf(smaller), instOf(bigger), createTermOrdering(),
            numbers);
    }

    protected static Feature literalsSmallerThan(String smaller, String bigger,
            IntegerLDT numbers) {
        return LiteralsSmallerThanFeature.create(instOf(smaller), instOf(bigger),
            createTermOrdering(), numbers);
    }

    /**
     * Create a projection of taclet applications to the instantiation of the trigger variable of a
     * taclet. If the trigger variable is not instantiated for a particular taclet app, an error
     * will be raised
     *
     * @return projection of taclet applications
     */
    protected static ProjectionToTerm instOfTriggerVariable() {
        return new TriggerVariableInstantiationProjection();
    }

    protected static ProjectionToTerm opTerm(Operator op,
            ProjectionToTerm[] subTerms) {
        return TermConstructionProjection.create(op, subTerms);
    }

    protected static ProjectionToTerm opTerm(Operator op,
            ProjectionToTerm subTerm) {
        return opTerm(op, new ProjectionToTerm[] { subTerm });
    }

    protected static ProjectionToTerm opTerm(Operator op,
            ProjectionToTerm subTerm0,
            ProjectionToTerm subTerm1) {
        return opTerm(op, new ProjectionToTerm[] { subTerm0, subTerm1 });
    }

    protected static Feature isTriggerVariableInstantiated() {
        return TriggerVarInstantiatedFeature.create();
    }

    protected static TermFeature opBase(ParametricFunctionDecl base) {
        return ParametricFunctionBaseTermFeature.create(base);
    }

    protected static TermFeature some(TermFeature f) {
        return not(rec(any(), not(f)));
    }

    protected static TermFeature eq(
            org.key_project.prover.strategy.costbased.termProjection.TermBuffer t) {
        return EqTermFeature.create(t, RenamingTermProperty.RENAMING_TERM_PROPERTY);
    }

    protected static Feature eq(ProjectionToTerm t1, ProjectionToTerm t2) {
        final TermBuffer buf = new TermBuffer();
        return let(buf, t1, applyTF(t2, eq(buf)));
    }

    protected static Feature directlyBelowSymbolAtIndex(Operator symbol, int index) {
        return directlyBelowSymbolAtIndex(op(symbol), index);
    }

    public static Feature directlyBelowSymbolAtIndex(TermFeature symbolTF, int index) {
        final var oneUp = FocusProjection.create(1);
        if (index == -1) {
            return add(not(FindAtTopLevelFeature.getInstance()), applyTF(oneUp, symbolTF));
        }
        return add(not(FindAtTopLevelFeature.getInstance()),
            ifZero(applyTF(oneUp, symbolTF), eq(sub(oneUp, index), FocusProjection.create()),
                inftyConst()));
    }

    protected static Feature contains(ProjectionToTerm bigTerm,
            ProjectionToTerm searchedTerm) {
        final TermBuffer buf = new TermBuffer();
        return let(buf, searchedTerm, applyTF(bigTerm, not(rec(any(), not(eq(buf))))));
    }

    protected static Feature isSubSortFeature(ProjectionToTerm s1,
            ProjectionToTerm s2) {
        return SortComparisonFeature.create(s1, s2, SortComparisonFeature.SUBSORT);
    }

    // Specific features

    protected static Feature implicitCastNecessary(ProjectionToTerm s1) {
        return ImplicitCastNecessary.create(s1);
    }

    protected static Feature isSelectSkolemConstantTerm(String svName) {
        return applyTF(svName, selectSkolemConstantTermFeature());
    }

    public static TermFeature selectSkolemConstantTermFeature() {
        return add(OperatorClassTF.create(Function.class),
            constantTermFeature(),
            hasLabel(ParameterlessTermLabel.SELECT_SKOLEM_LABEL));
    }

    public static TermFeature hasLabel(TermLabel label) {
        return TermPredicateTermFeature.create(
            (t -> t instanceof JTerm jTerm &&
                    jTerm.containsLabel(label)));
    }

    protected static TermFeature anonHeapTermFeature() {
        return add(OperatorClassTF.create(Function.class),
            constantTermFeature(), hasLabel(ParameterlessTermLabel.ANON_HEAP_LABEL));
    }

    protected static Feature print(Feature f) {
        return new PrintFeature(f);
    }

    protected static Feature print(String msg, Feature f) {
        return new PrintFeature(msg, f);
    }
}
