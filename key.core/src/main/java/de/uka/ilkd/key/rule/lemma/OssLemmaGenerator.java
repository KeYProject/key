/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.HexFormat;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.proof.io.OutputStreamProofSaver;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.Modality;
import org.key_project.prover.rules.ApplicationRestriction;
import org.key_project.prover.rules.RuleAbortException;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;

/**
 * Lemma generator capturing an aggregated one-step-simplification as a taclet: for a top level
 * formula {@code F} that the {@link OneStepSimplifier} would simplify to {@code F'} using the
 * context formulas {@code phi_1, ..., phi_k}, it produces the ground taclet
 *
 * <pre>
 * ossLemma_&lt;hash&gt; {
 *     \assumes (phi_a1, ... ==&gt; phi_s1, ...)   // the used context formulas, by polarity
 *     \find (F) \replacewith (F')
 *     \inSequentState                            // only if the assumes clause is nonempty
 * }
 * </pre>
 *
 * The pure rewrite steps aggregated by the simplifier are state-independent equivalences; the
 * replace-known steps are only valid where the assumed formulas hold, which is exactly what the
 * {@code \assumes} clause combined with the {@code \inSequentState} restriction enforces (the
 * simplifier itself stops replace-known at update and modality boundaries). Without replace-known
 * steps the taclet is an unrestricted equivalence rewrite.
 *
 * <p>
 * The taclet name is derived from a canonical serialization of find, assumptions, and
 * replacewith, so replaying the introducing rule application reproduces the name, and a changed
 * simplifier result surfaces as a missing taclet instead of a silently different rewrite.
 *
 * <p>
 * Formulas containing modal operators are not accepted: their taclets would fall outside the
 * fragment supported by the taclet soundness proof obligation machinery. Symbolic execution
 * formulas remain the business of the stock one step simplifier.
 */
@NullMarked
public final class OssLemmaGenerator implements LemmaTacletGenerator {

    public static final OssLemmaGenerator INSTANCE = new OssLemmaGenerator();

    private static final Name NAME = new Name("ossLemma");

    private OssLemmaGenerator() {
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        if (!pio.isTopLevel()) {
            return false;
        }
        final GeneratedLemmaRegistry registry =
            GeneratedLemmaRegistry.getIfPresent(goal.proof());
        if (registry != null && registry.isVetoed(pio.sequentFormula())) {
            return false;
        }
        final OneStepSimplifier simplifier = MiscTools.findOneStepSimplifier(goal.proof());
        return simplifier != null && simplifier.canSimplify(goal, pio)
                && !containsModality(pio.sequentFormula().formula());
    }

    @Override
    public RewriteTaclet generate(Goal goal, PosInOccurrence pio) {
        final Services services = goal.proof().getServices();
        final OneStepSimplifier simplifier = MiscTools.findOneStepSimplifier(goal.proof());
        if (simplifier == null) {
            throw new IllegalStateException(
                "no one step simplifier found in profile of proof " + goal.proof().name());
        }
        final OneStepSimplifier.SimplificationResult result =
            simplifier.computeSimplification(goal, pio, new OneStepSimplifier.Protocol());
        if (result == null) {
            GeneratedLemmaRegistry.get(goal.proof()).veto(pio.sequentFormula());
            throw new RuleAbortException("one step simplification of "
                + pio.sequentFormula().formula()
                + " produced no result (is the one step simplifier active for this proof?)");
        }

        final JTerm find = (JTerm) pio.sequentFormula().formula();
        final JTerm simplified = (JTerm) result.simplified().formula();

        if (RENAMING_TERM_PROPERTY.equalsModThisProperty(find, simplified)) {
            // the aggregated simplification only shuffles term labels or bound variable names;
            // a lemma \find(F) \replacewith(F') with F == F' modulo those is worthless and,
            // under automation, a source of non-termination
            GeneratedLemmaRegistry.get(goal.proof()).veto(pio.sequentFormula());
            throw new RuleAbortException(
                "one step simplification changes " + find + " only up to renaming/term labels");
        }

        ImmutableList<SequentFormula> assumesAntec = ImmutableList.nil();
        ImmutableList<SequentFormula> assumesSucc = ImmutableList.nil();
        for (final PosInOccurrence context : result.usedContextFormulas()) {
            if (context.isInAntec()) {
                assumesAntec = assumesAntec.append(context.sequentFormula());
            } else {
                assumesSucc = assumesSucc.append(context.sequentFormula());
            }
        }

        final RewriteTacletBuilder<RewriteTaclet> tb = new RewriteTacletBuilder<>();
        // the content hash is a human-recognizable prefix only; uniqueness comes from the
        // introduction node's tree-structural id. Formulas on sibling branches can be equal in
        // their printed form yet contain distinct proof-local symbol instances (program
        // variables, skolem constants) sharing the same name, so a purely content-derived name
        // would alias semantically different lemmas across branches. The node id is
        // replay-stable (path and introduced-rule count), so replaying the introduction
        // regenerates the same name.
        tb.setName(MiscTools.toValidTacletName(
            contentHashName(services, find, assumesAntec, assumesSucc, simplified) + "_"
                + goal.node().getUniqueTacletId()));
        tb.setDisplayName(NAME.toString());
        tb.setFind(find);
        tb.addGoalTerm(simplified);
        tb.addRuleSet(new RuleSet(new Name("concrete")));
        if (!assumesAntec.isEmpty() || !assumesSucc.isEmpty()) {
            tb.setAssumesSequent(JavaDLSequentKit.createSequent(assumesAntec, assumesSucc));
            tb.setApplicationRestriction(
                new ApplicationRestriction(ApplicationRestriction.IN_SEQUENT_STATE));
        }
        try {
            return tb.getTaclet();
        } catch (RuleAbortException e) {
            throw e;
        } catch (RuntimeException e) {
            // taclet construction can be rejected for reasons rooted in taclet wellformedness
            // checks; a failure must never abort automated proof search, so the formula is
            // vetoed (no further introduction attempts) and the application aborted cleanly
            GeneratedLemmaRegistry.get(goal.proof()).veto(pio.sequentFormula());
            throw new RuleAbortException(
                "generating a lemma taclet for " + find + " failed: " + e.getMessage());
        }
    }

    /**
     * returns true iff the term contains a modal operator anywhere; such formulas fall outside
     * the fragment supported by the taclet soundness proof obligation machinery and are
     * therefore not lemma-eligible
     */
    public static boolean containsModality(Term term) {
        if (term.op() instanceof Modality) {
            return true;
        }
        for (final Term sub : term.subs()) {
            if (containsModality(sub)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Derives the taclet name from a canonical serialization of the taclet content. The printed
     * form is used instead of hash codes of the terms, since the latter are not guaranteed to be
     * stable across JVM runs, and replay resolves the taclet by name.
     */
    private static String contentHashName(Services services, JTerm find,
            ImmutableList<SequentFormula> assumesAntec, ImmutableList<SequentFormula> assumesSucc,
            JTerm replacewith) {
        final StringBuilder content = new StringBuilder();
        content.append("find:").append(OutputStreamProofSaver.printTerm(find, services));
        for (final SequentFormula sf : assumesAntec) {
            content.append("\nassumeA:")
                    .append(OutputStreamProofSaver.printTerm((JTerm) sf.formula(), services));
        }
        for (final SequentFormula sf : assumesSucc) {
            content.append("\nassumeS:")
                    .append(OutputStreamProofSaver.printTerm((JTerm) sf.formula(), services));
        }
        content.append("\nreplacewith:")
                .append(OutputStreamProofSaver.printTerm(replacewith, services));

        try {
            final MessageDigest digest = MessageDigest.getInstance("SHA-256");
            final byte[] hash = digest.digest(content.toString().getBytes(StandardCharsets.UTF_8));
            return NAME + "_" + HexFormat.of().formatHex(hash, 0, 6);
        } catch (NoSuchAlgorithmException e) {
            throw new IllegalStateException("SHA-256 not available", e);
        }
    }
}
