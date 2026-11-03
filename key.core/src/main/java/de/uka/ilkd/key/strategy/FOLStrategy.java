/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.strategy.feature.*;
import de.uka.ilkd.key.strategy.quantifierHeuristics.*;
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
import org.key_project.prover.strategy.IFormulaTermFeatures;
import org.key_project.prover.strategy.costbased.*;
import org.key_project.prover.strategy.costbased.feature.*;
import org.key_project.prover.strategy.costbased.quantifierHeuristics.TriggerTreatment;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

import org.jspecify.annotations.NonNull;

import static de.uka.ilkd.key.strategy.StaticFeatureCollection.*;

/// Strategy for general FOL rules. This does not consider other
/// theories like integers or Java-specific functions.
///
/// In particular, instantiation of quantifiers is not supported by this
/// strategy, as the current E-matching depends on the theory of integers.
/// For that reason, instantiation can be found [JFOLStrategy].
public class FOLStrategy extends org.key_project.prover.strategy.FOLStrategy<Goal>
        implements ComponentStrategy<Goal> {

    protected final StrategyProperties strategyProperties;
    private final Proof proof;

    public FOLStrategy(ArithTermFeatures tf, IFormulaTermFeatures ff, Proof proof,
            StrategyProperties strategyProperties) {
        super(tf, ff, new JavaFeatureConstants(),
            proof.getServices().getTypeConverter().getIntegerLDT());

        this.proof = proof;
        this.strategyProperties = strategyProperties.clone();
        initDispatchersAndFeatures();
    }

    @Override
    protected Feature setUpGlobalF(RuleSetDispatchFeature d) {
        final Feature oneStepSimplificationF =
            oneStepSimplificationFeature(CostBand.REWRITE.cost());
        return add(d, oneStepSimplificationF);
    }

    private Feature oneStepSimplificationFeature(Feature cost) {
        SetRuleFilter filter = new SetRuleFilter();
        filter.addRuleToSet(MiscTools.findOneStepSimplifier(proof));
        return ConditionalFeature.createConditional(filter, cost);
    }


    @Override
    protected RuleSetDispatchFeature setupCostComputationF(RuleSetDispatchFeature d) {
        d = super.setupCostComputationF(d);
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

        return d;
    }

    /** the value of the trigger option, fixed when this strategy was constructed */
    protected String triggersOption() {
        return strategyProperties.getProperty(StrategyProperties.TRIGGERS_OPTIONS_KEY);
    }

    @Override
    protected TriggerTreatment triggerTreatment() {
        if (StrategyProperties.TRIGGERS_CLASSIC.equals(triggersOption())) {
            return TriggerTreatment.CLASSIC;
        }
        return StrategyProperties.TRIGGERS_GOOD.equals(triggersOption()) ? TriggerTreatment.GOOD
                : TriggerTreatment.BEST;
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
