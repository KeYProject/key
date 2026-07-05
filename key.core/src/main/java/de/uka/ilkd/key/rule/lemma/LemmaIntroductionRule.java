/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.DefaultBuiltInRuleApp;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.Name;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Built-in rule that introduces a taclet computed by a {@link LemmaTacletGenerator} as a
 * goal-local rule.
 *
 * <p>
 * The rule performs the <em>introduction step</em> only: it makes the generated taclet available
 * on the resulting goal (registered with a {@link GeneratedLemmaJustification} pointing to its
 * soundness proof obligation) but does not change the sequent. Actually rewriting with the lemma
 * is an ordinary, separately recorded taclet application — this two-step structure is what makes
 * the transformation inspectable and replayable.
 *
 * <p>
 * On proof replay, replaying an application of this rule re-runs the generator; since generators
 * are deterministic in the term at the application position, the regenerated taclet carries the
 * same name and the subsequent taclet application resolves against it.
 */
@NullMarked
public abstract class LemmaIntroductionRule implements BuiltInRule {

    private final LemmaTacletGenerator generator;
    private final Name name;

    protected LemmaIntroductionRule(LemmaTacletGenerator generator) {
        this.generator = generator;
        this.name = new Name("introduce_" + generator.name());
    }

    public LemmaTacletGenerator getGenerator() {
        return generator;
    }

    @Override
    public Name name() {
        return name;
    }

    @Override
    public String toString() {
        return displayName();
    }

    /**
     * {@inheritDoc}
     *
     * <p>
     * The result must depend only on the formula at the position (and formula-keyed state such
     * as the generator's veto bookkeeping), never on the goal-local rule indices: built-in rule
     * applications are queued and may be executed after further rules changed the goal, and
     * proof replay re-evaluates applicability freshly at the recorded position. An
     * index-dependent condition would make recorded introductions unreplayable whenever the
     * queued application was executed after the condition had changed. As a consequence, an
     * introduction may occasionally be redundant (an equivalent lemma is already available);
     * this is harmless, since lemma names are unique per introduction.
     */
    @Override
    public boolean isApplicable(Goal goal, @Nullable PosInOccurrence pio) {
        return pio != null && generator.isApplicable(goal, pio);
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return true;
    }

    @Override
    public IBuiltInRuleApp createApp(@Nullable PosInOccurrence pos, TermServices services) {
        return new DefaultBuiltInRuleApp<>(this, pos);
    }

    @Override
    public @NonNull ImmutableList<Goal> apply(Goal goal, RuleApp ruleApp) {
        final PosInOccurrence pio = ruleApp.posInOccurrence();
        final GeneratedLemma lemma =
            GeneratedLemmaRegistry.get(goal.proof()).getOrCreate(goal, pio, generator);

        final ImmutableList<Goal> newGoals = goal.split(1);
        final Goal newGoal = newGoals.head();
        final NoPosTacletApp tacletApp = NoPosTacletApp.createFixedNoPosTacletApp(lemma.taclet(),
            SVInstantiations.EMPTY_SVINSTANTIATIONS, goal.proof().getServices());
        assert tacletApp != null : "generated lemma taclet could not be turned into a taclet app";
        newGoal.addNoPosTacletApp(tacletApp);
        return newGoals;
    }
}
