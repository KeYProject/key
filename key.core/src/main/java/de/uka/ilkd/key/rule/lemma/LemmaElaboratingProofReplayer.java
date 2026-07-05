/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import java.util.HashSet;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.IntermediateProofReplayer;
import de.uka.ilkd.key.proof.replay.CopyingProofReplayer;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

/**
 * A-posteriori proof elaboration ("mode 2" of the taclet-generating transformer approach): copies
 * a proof onto a fresh proof of the same problem, replacing every eligible application of the one
 * step simplifier by the two-step lemma form — an introduction of the generated taclet (see
 * {@link OssLemmaGenerator}) followed by an ordinary application of that taclet.
 *
 * <p>
 * This decouples proof search from transparency: the proof is found with the fast opaque rule,
 * and the finished proof is then elaborated into a form in which every aggregated simplification
 * is a declarative, separately provable artifact. Simplifier applications that cannot be
 * elaborated (formulas containing modal operators, or positions that cannot be relocated) are
 * copied unchanged, so elaboration never fails a proof that copies cleanly.
 */
public class LemmaElaboratingProofReplayer extends CopyingProofReplayer {

    private int elaborated = 0;
    private int copiedOss = 0;

    public LemmaElaboratingProofReplayer(Proof originalProof, Proof target) {
        super(originalProof, target);
    }

    /**
     * Elaborates the original proof onto the target proof (a fresh proof of the same problem,
     * open at its root).
     *
     * @param original the proof to elaborate
     * @param target the fresh target proof; must have the same root sequent
     * @return the replayer, for querying {@link #getElaboratedCount()} and
     *         {@link #getCopiedOssCount()}
     */
    public static LemmaElaboratingProofReplayer elaborate(Proof original, Proof target)
            throws IntermediateProofReplayer.BuiltInConstructionException {
        final LemmaElaboratingProofReplayer replayer =
            new LemmaElaboratingProofReplayer(original, target);
        replayer.copy(original.root(), target.getOpenGoal(target.root()), new HashSet<>());
        return replayer;
    }

    /**
     * returns the number of one step simplifier applications replaced by introduction plus
     * taclet application
     */
    public int getElaboratedCount() {
        return elaborated;
    }

    /**
     * returns the number of one step simplifier applications copied unchanged (not
     * lemma-eligible)
     */
    public int getCopiedOssCount() {
        return copiedOss;
    }

    @Override
    protected ImmutableList<Goal> reApplyRuleApp(Node node, Goal openGoal)
            throws IntermediateProofReplayer.BuiltInConstructionException {
        if (node.getAppliedRuleApp() instanceof OneStepSimplifierRuleApp ossApp
                && ossApp.posInOccurrence() != null) {
            final PosInOccurrence pos =
                findInNewSequent(ossApp.posInOccurrence(), openGoal.sequent());
            if (pos != null
                    && OssLemmaIntroductionRule.INSTANCE.isApplicable(openGoal, pos)) {
                final ImmutableList<Goal> result = elaborateOssStep(openGoal, pos);
                if (result != null) {
                    elaborated++;
                    return result;
                }
            }
            copiedOss++;
        }
        return super.reApplyRuleApp(node, openGoal);
    }

    /**
     * Replaces one simplifier application by lemma introduction plus taclet application.
     * Returns the resulting goals, or {@code null} if the introduction is not possible (in which
     * case the goal is untouched and the caller falls back to copying the original step).
     */
    private ImmutableList<Goal> elaborateOssStep(Goal openGoal, PosInOccurrence pos) {
        final var services = openGoal.proof().getServices();

        final ImmutableList<Goal> afterIntro = openGoal
                .apply(OssLemmaIntroductionRule.INSTANCE.createApp(pos, services));
        if (afterIntro == null) {
            return null;
        }
        final Goal introGoal = afterIntro.head();

        // the taclet introduced by the step just performed
        final var introducedRules = introGoal.node().getLocalIntroducedRules().iterator();
        if (!introducedRules.hasNext()) {
            throw new IllegalStateException(
                "lemma introduction did not introduce a taclet at " + pos);
        }
        final NoPosTacletApp lemmaApp = introducedRules.next();

        // the introduction step leaves the sequent unchanged, so the position stays valid
        final NoPosTacletApp matched = lemmaApp.matchFind(pos, services);
        if (matched == null) {
            throw new IllegalStateException(
                "generated lemma " + lemmaApp.taclet().name() + " does not match at " + pos);
        }
        TacletApp application = matched.setPosInOccurrence(pos, services);
        if (!application.complete()) {
            final ImmutableList<TacletApp> instantiated =
                application.findIfFormulaInstantiations(introGoal.sequent(), services);
            if (instantiated.isEmpty()) {
                throw new IllegalStateException("no assumption instantiation found for lemma "
                    + lemmaApp.taclet().name() + " although it was generated from this sequent");
            }
            application = instantiated.head();
        }
        return introGoal.apply(application);
    }

}
