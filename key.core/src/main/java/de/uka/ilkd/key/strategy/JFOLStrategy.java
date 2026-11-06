/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.strategy.feature.EqNonDuplicateAppFeature;
import de.uka.ilkd.key.strategy.feature.JavaFeatureConstants;
import de.uka.ilkd.key.strategy.feature.TopLevelFindFeature;
import de.uka.ilkd.key.strategy.quantifierHeuristics.ClausesSmallerThanFeature;
import de.uka.ilkd.key.strategy.termProjection.TermBuffer;
import de.uka.ilkd.key.strategy.termfeature.ContainsExecutableCodeTermFeature;
import de.uka.ilkd.key.strategy.termgenerator.SuperTermGenerator;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.TermOrdering;
import org.key_project.prover.proof.rulefilter.SetRuleFilter;
import org.key_project.prover.rules.IBuiltInRule;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.strategy.ArithTermFeatures;
import org.key_project.prover.strategy.ComponentStrategy;
import org.key_project.prover.strategy.FOLStrategy;
import org.key_project.prover.strategy.IFormulaTermFeatures;
import org.key_project.prover.strategy.costbased.CostBand;
import org.key_project.prover.strategy.costbased.feature.ConditionalFeature;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.feature.RuleSetDispatchFeature;
import org.key_project.prover.strategy.costbased.feature.SumFeature;
import org.key_project.prover.strategy.costbased.quantifierHeuristics.TriggerTreatment;
import org.key_project.prover.strategy.costbased.termProjection.FocusProjection;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

import org.jspecify.annotations.NonNull;

import static de.uka.ilkd.key.strategy.StaticFeatureCollection.*;
import static org.key_project.prover.strategy.costbased.quantifierHeuristics.TriggerTreatment.*;

/// This strategy extends the classical [FOLStrategy] with heuristics
/// for quantifier instantiation based on E-matching, which involves
/// normalization of quantified formulas, as well as term features depending on
/// integer theory.
///
/// Do not create directly; use [JFOLStrategyFactory] instead.
public class JFOLStrategy extends FOLStrategy<Goal> implements ComponentStrategy<Goal> {
    public static final Name NAME = new Name("JFOL Strategy");
    protected final StrategyProperties strategyProperties;

    private final ArithTermFeatures tf;
    private final Proof proof;

    public JFOLStrategy(ArithTermFeatures tf, IFormulaTermFeatures ff, Proof proof,
            StrategyProperties strategyProperties) {
        super(ff, new JavaFeatureConstants(),
            oneStepSimplificationFeature(proof, CostBand.REWRITE.cost()));
        this.tf = tf;
        this.proof = proof;
        this.strategyProperties = strategyProperties.clone();
        init();
    }

    private static Feature oneStepSimplificationFeature(Proof proof, Feature cost) {
        SetRuleFilter filter = new SetRuleFilter();
        filter.addRuleToSet(MiscTools.findOneStepSimplifier(proof));
        return ConditionalFeature.createConditional(filter, cost);
    }

    @Override
    protected void setupFormulaNormalisation(RuleSetDispatchFeature d) {
        super.setupFormulaNormalisation(d);
        var numbers = getServices().getTypeConverter().getIntegerLDT();
        bindRuleSet(d, "cnf_orComm",
            SumFeature.createSum(applyTF("commRight", ff.clause()),
                applyTFNonStrict("commResidue", ff.clauseSet()),
                or(applyTF("commLeft", ff.andF()),
                    add(applyTF("commLeft", ff.literal()),
                        literalsSmallerThan("commRight", "commLeft", numbers))),
                longConst(-100)));
        bindRuleSet(d, "cnf_andComm",
            SumFeature.createSum(applyTF("commLeft", ff.clause()),
                applyTF("commRight", ff.clauseSet()),
                applyTFNonStrict("commResidue", ff.clauseSet()),
                // at least one of the subformulas has to be a literal;
                // otherwise, sorting is not likely to have any big effect
                ifZero(
                    add(applyTF("commLeft", not(ff.literal())),
                        applyTF("commRight", rec(ff.andF(), not(ff.literal())))),
                    longConst(100), longConst(-60)),
                clausesSmallerThan("commRight", "commLeft", numbers)));
    }

    @Override
    protected void setupSplitting(RuleSetDispatchFeature d) {
        super.setupSplitting(d);
        var heapLDT = getServices().getTypeConverter().getHeapLDT();
        var vf = new ValueTermFeature(op(heapLDT.getNull()));
        ProjectionToTerm<Goal> cutFormula = instOf("cutFormula");
        bindRuleSet(d, "cut_direct",
            SumFeature
                    .createSum(
                        ifZero(notBelowQuantifier(),
                            add(
                                // prefer cuts over "something = null"
                                ifZero(applyTF(FocusProjection.<Goal>create(),
                                    opSub(tf.eq, any(), vf.nullTerm)),
                                    longConst(-5), longConst(0)),
                                // punish cuts over formulas containing anon heap functions
                                ifZero(applyTF(cutFormula, rec(any(), not(anonHeapTermFeature()))),
                                    longConst(0), longConst(1000))))));
    }

    private Feature clausesSmallerThan(String smaller, String bigger, IntegerLDT numbers) {
        return ClausesSmallerThanFeature.create(instOf(smaller), instOf(bigger),
            createTermOrdering(), numbers);
    }

    /** the value of the trigger option, fixed when this strategy was constructed */
    @Override
    protected String triggersOption() {
        return strategyProperties.getProperty(StrategyProperties.TRIGGERS_OPTIONS_KEY);
    }

    @Override
    protected TriggerTreatment triggerTreatment() {
        return forOption(triggersOption());
    }

    public TriggerTreatment forOption(String option) {
        if (StrategyProperties.TRIGGERS_CLASSIC.equals(option)) {
            return CLASSIC;
        }
        return StrategyProperties.TRIGGERS_GOOD.equals(option) ? GOOD : BEST;
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    protected void setupCostComputationF(RuleSetDispatchFeature d) {
        super.setupCostComputationF(d);
        bindRuleSet(d, "simplify_instanceof_static",
            add(EqNonDuplicateAppFeature.INSTANCE, CostBand.PREFER.cost()));

        bindRuleSet(d, "evaluate_instanceof", CostBand.PREFER.cost());

        bindRuleSet(d, "instanceof_to_exists", TopLevelFindFeature.ANTEC);

        // delete cast
        bindRuleSet(d, "cast_deletion",
            ifZero(implicitCastNecessary(instOf("castedTerm")),
                CostBand.NORMALIZE.cost(),
                inftyConst()));

        bindRuleSet(d, "type_hierarchy_def", CostBand.TYPE.at(-500));
    }

    @Override
    protected boolean instQuantifiersWithQueries() {
        return StrategyProperties.QUANTIFIERS_INSTANTIATE
                .equals(strategyProperties.getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY));
    }

    @Override
    protected boolean quantifiersMightSplit() {
        return StrategyProperties.QUANTIFIERS_INSTANTIATE
                .equals(strategyProperties.getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY))
                || StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS.equals(
                    strategyProperties.getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY));
    }

    @Override
    protected Feature allowQuantifierSplitting() {
        if (StrategyProperties.QUANTIFIERS_INSTANTIATE.equals(
            strategyProperties.getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY))) {
            return longConst(0);
        }
        if (StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS.equals(
            strategyProperties.getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY))) {
            return sequentContainsNoPrograms();
        }
        return inftyConst();
    }

    @Override
    protected boolean quantifierInstantiatedEnabled() {
        return !StrategyProperties.QUANTIFIERS_NONE
                .equals(strategyProperties.getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY));
    }

    @Override
    protected Feature allowSplitting(ProjectionToTerm<Goal> focus) {
        if (normalSplitting()) {
            return longConst(0);
        }
        if (StrategyProperties.SPLITTING_DELAYED
                .equals(strategyProperties.getProperty(StrategyProperties.SPLITTING_OPTIONS_KEY))) {
            return or(applyTF(focus, ContainsExecutableCodeTermFeature.PROGRAMS),
                sequentContainsNoPrograms());
        }
        // else: SPLITTING_OFF
        return applyTF(focus, ContainsExecutableCodeTermFeature.PROGRAMS);
    }

    @Override
    protected boolean normalSplitting() {
        return StrategyProperties.SPLITTING_NORMAL
                .equals(strategyProperties.getProperty(StrategyProperties.SPLITTING_OPTIONS_KEY));
    }

    @Override
    protected Services getServices() {
        return proof.getServices();
    }

    @Override
    protected TermOrdering createTermOrdering() {
        return StaticFeatureCollection.createTermOrdering();
    }

    @Override
    public boolean isResponsibleFor(IBuiltInRule<Goal> rule) {
        return rule instanceof OneStepSimplifier;
    }

    @Override
    protected RuleSet getHeuristic(String p_name) {
        final NamespaceSet nss = proof.getNamespaces();
        final Namespace<@NonNull RuleSet> ns = nss.ruleSets();
        final RuleSet h = ns.lookup(new Name(p_name));

        assert h != null : "Did not find the rule set " + p_name;

        return h;
    }

    @Override
    protected Feature isBelow(TermFeature t) {
        final TermBuffer superTerm = new TermBuffer();
        return not(sum(superTerm, SuperTermGenerator.upwards(any(), proof.getServices()),
            not(applyTF(superTerm, t))));
    }
}
