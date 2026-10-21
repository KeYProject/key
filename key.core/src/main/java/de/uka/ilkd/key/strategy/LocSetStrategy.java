/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.feature.MatchedAssumesFeature;
import de.uka.ilkd.key.strategy.feature.PolynomialValuesCmpFeature;
import de.uka.ilkd.key.strategy.termProjection.FocusFormulaProjection;
import de.uka.ilkd.key.strategy.termgenerator.SuperTermGenerator;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.IBuiltInRule;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.AbstractFeatureStrategy;
import org.key_project.prover.strategy.ComponentStrategy;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.feature.RuleSetDispatchFeature;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/// Strategy for location sets
/// Do not create directly; use [SetStrategyFactory] instead.
public class LocSetStrategy extends AbstractFeatureStrategy<Goal>
        implements ComponentStrategy<Goal> {
    public static final Name NAME = new Name("LocSet Strategy");

    private final RuleSetDispatchFeature costComputationDispatcher;

    private final boolean stopAtFirstNonCloseableGoal;
    private final LocSetTermFeatures lsf;
    private final Proof proof;

    public LocSetStrategy(Proof proof, StrategyProperties strategyProperties) {
        this.proof = proof;
        TypeConverter typeConverter = proof.getServices().getTypeConverter();
        this.lsf = new LocSetTermFeatures(
            typeConverter.getLDT(de.uka.ilkd.key.ldt.SetLDT.class),
            typeConverter.getLocSetLDT(),
            typeConverter.getHeapLDT());
        costComputationDispatcher = setupCostComputationF();

        stopAtFirstNonCloseableGoal =
            strategyProperties.getProperty(StrategyProperties.STOPMODE_OPTIONS_KEY)
                    .equals(StrategyProperties.STOPMODE_NONCLOSE);
    }

    private RuleSetDispatchFeature setupCostComputationF() {
        final RuleSetDispatchFeature d = new RuleSetDispatchFeature();
        /// ensures that blasting rules are only applied if the focus formula
        /// contains a constructor whose rules need to decompose a locations
        /// avoid split up
        /// at the moment it is not as general as it could be, e.g. it ignores equalities in the
        /// rest of the sequent (e.g, ==> l \in allObjects(f) would lead to an application but
        /// allObjects(f) = EQ ==> l \in EQ not)
        bindRuleSet(d, "locSetEqualityBlastingRight",
            ifZero(applyTF(FocusFormulaProjection.INSTANCE, lsf.requireLocationDecomposition),
                longConst(-100), longConst(-80)));

        bindRuleSet(d, "locSetArrayRangeMerge",
            add(ifZero(MatchedAssumesFeature.INSTANCE,
                add(PolynomialValuesCmpFeature.leq(instOf("lower"), instOf("upper")),
                    PolynomialValuesCmpFeature.lt(instOf("upper"), instOf("lower2")),
                    PolynomialValuesCmpFeature.leq(instOf("lower2"), instOf("upper2"))),
                longConst(0)),
                longConst(-4000)));

        bindRuleSet(d, "locSetArrayRangeInterNested",
            add(ifZero(MatchedAssumesFeature.INSTANCE,
                add(PolynomialValuesCmpFeature.leq(instOf("lower"), instOf("lower2")),
                    PolynomialValuesCmpFeature.leq(instOf("upper2"), instOf("upper"))),
                longConst(0)),
                longConst(-4000)));

        bindRuleSet(d, "locSetArrayRangeInterNested2",
            add(ifZero(MatchedAssumesFeature.INSTANCE,
                add(PolynomialValuesCmpFeature.leq(instOf("lower2"), instOf("lower")),
                    PolynomialValuesCmpFeature.leq(instOf("upper"), instOf("upper2"))),
                longConst(0)),
                longConst(-4000)));

        bindRuleSet(d, "locSetArrayRangeInterDisjoint",
            add(ifZero(MatchedAssumesFeature.INSTANCE,
                PolynomialValuesCmpFeature.lt(instOf("upper"), instOf("lower2")),
                longConst(0)),
                longConst(-4000)));

        bindRuleSet(d, "locSetArrayRangeInterDisjoint2",
            add(ifZero(MatchedAssumesFeature.INSTANCE,
                PolynomialValuesCmpFeature.lt(instOf("upper2"), instOf("lower")),
                longConst(0)),
                longConst(-4000)));
        return d;
    }

    @Override
    public boolean isResponsibleFor(RuleSet rs) {
        return costComputationDispatcher.get(rs) != null;
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return stopAtFirstNonCloseableGoal;
    }

    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        return true;
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
    public <GOAL extends ProofGoal<GOAL>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, GOAL goal, MutableState mState) {
        return this.costComputationDispatcher.computeCost(app, pos, goal, mState);
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
        return aspect == StrategyAspect.Cost ? costComputationDispatcher : null;
    }

    @Override
    public boolean isResponsibleFor(IBuiltInRule<Goal> rule) {
        return false;
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
        final de.uka.ilkd.key.strategy.termProjection.TermBuffer superTerm =
            new de.uka.ilkd.key.strategy.termProjection.TermBuffer();
        return not(sum(superTerm, SuperTermGenerator.upwards(any(), proof.getServices()),
            not(applyTF(superTerm, t))));
    }
}
