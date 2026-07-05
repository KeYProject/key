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
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.Name;
import org.key_project.prover.proof.rulefilter.TacletFilter;
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

    @Override
    public boolean isApplicable(Goal goal, @Nullable PosInOccurrence pio) {
        return pio != null && generator.isApplicable(goal, pio)
                && !lemmaAlreadyAvailable(goal, pio);
    }

    /**
     * Checks whether a lemma taclet of this generator is already available and usable at the
     * given position. In that case the introduction is not offered again: re-introduction would
     * be redundant, and — since the introduction step does not change the sequent — automated
     * application would not terminate without this check.
     */
    private boolean lemmaAlreadyAvailable(Goal goal, PosInOccurrence pio) {
        final var services = goal.proof().getServices();
        final ImmutableList<NoPosTacletApp> candidates = goal.indexOfTaclets()
                .getRewriteTaclet(pio, GENERATED_BY_THIS_GENERATOR, services);
        for (final NoPosTacletApp candidate : candidates) {
            if (candidate.taclet().assumesSequent().isEmpty()) {
                return true;
            }
            // assumption-carrying lemmas count as available only if their assumptions can
            // actually be instantiated in the current sequent
            final TacletApp positioned = candidate.setPosInOccurrence(pio, services);
            if (positioned != null && (positioned.complete() || !positioned
                    .findIfFormulaInstantiations(goal.sequent(), services).isEmpty())) {
                return true;
            }
        }
        return false;
    }

    private final TacletFilter GENERATED_BY_THIS_GENERATOR = new TacletFilter() {
        @Override
        protected boolean filter(org.key_project.prover.rules.Taclet taclet) {
            return generator.name().toString().equals(taclet.displayName());
        }
    };

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
