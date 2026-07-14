/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.taclettranslation.lemma.AutomaticProver;

import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.prover.rules.ApplicationRestriction;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * End-to-end tests for {@link OssLemmaGenerator}: aggregated one-step-simplifications are
 * captured as generated taclets, their soundness proof obligations are created and discharged,
 * and the proofs replay after save/reload. Covered are a context-free simplification of an
 * update-laden formula (pure equivalence rewrite, proof obligation containing updates) and a
 * replace-known simplification (taclet with {@code \assumes} clause and in-sequent-state
 * restriction, applied with assumption instantiation).
 */
public class TestOssLemmaIntroduction {

    private static final Path TEST_CASE_DIRECTORY = FindResources.getTestCasesDirectory();

    /**
     * Applies the taclet of the given app at the given position, instantiating its assumptions
     * from the goal's sequent if necessary, and returns the resulting open goal.
     */
    private static Goal applyTaclet(Goal goal, NoPosTacletApp app, PosInOccurrence pos) {
        final Proof proof = goal.proof();
        final NoPosTacletApp matched = app.matchFind(pos, proof.getServices());
        assertNotNull(matched, "taclet " + app.taclet().name() + " does not match at " + pos);
        TacletApp positioned = matched.setPosInOccurrence(pos, proof.getServices());
        if (!positioned.complete()) {
            final var instantiated = positioned
                    .findIfFormulaInstantiations(goal.sequent(), proof.getServices());
            assertFalse(instantiated.isEmpty(),
                "no assumption instantiation found for " + app.taclet().name());
            positioned = instantiated.head();
        }
        goal.apply(positioned);
        return proof.openGoals().head();
    }

    @Test
    public void testOssLemmaWithAssumptions() throws Exception {
        final KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment
                .load(TEST_CASE_DIRECTORY.resolve("lemmagen").resolve("ossLemmaAssumes.key"));
        try {
            final Proof proof = env.getLoadedProof();
            assertNotNull(proof);
            OneStepSimplifier.refreshOSS(proof);

            // p -> ((q & true) & p) ==> after impRight ==> p ==> (q & true) & p
            final Goal root = proof.openGoals().head();
            final NoPosTacletApp impRight =
                root.indexOfTaclets().lookup(new Name("impRight"));
            assertNotNull(impRight);
            final Goal afterImp = applyTaclet(root, impRight, new PosInOccurrence(
                root.sequent().succedent().getFirst(), PosInTerm.getTopLevel(), false));

            // introduce the lemma at (q & true) & p; the simplification uses the context
            // formula p (replace-known), so the taclet carries an assumes clause and the
            // in-sequent-state restriction
            final PosInOccurrence target = new PosInOccurrence(
                afterImp.sequent().succedent().getFirst(), PosInTerm.getTopLevel(), false);
            assertTrue(OssLemmaIntroductionRule.INSTANCE.isApplicable(afterImp, target));
            afterImp.apply(
                OssLemmaIntroductionRule.INSTANCE.createApp(target, proof.getServices()));

            final GeneratedLemma lemma =
                GeneratedLemmaRegistry.get(proof).getLemmas().iterator().next();
            assertFalse(lemma.taclet().assumesSequent().isEmpty(),
                "replace-known was used, so the taclet must record its assumptions");
            assertEquals(1, lemma.taclet().assumesSequent().antecedent().size(),
                "exactly the context formula p is assumed (in the antecedent)");
            assertTrue(lemma.taclet().applicationRestriction()
                    .matches(ApplicationRestriction.IN_SEQUENT_STATE),
                "assumption-carrying lemmas must be restricted to the sequent state");

            // apply the lemma (with assumption instantiation): the formula becomes q
            final Goal afterIntro = proof.openGoals().head();
            final NoPosTacletApp lemmaApp =
                afterIntro.indexOfTaclets().lookup(lemma.taclet().name());
            assertNotNull(lemmaApp);
            final Goal afterApply = applyTaclet(afterIntro, lemmaApp, new PosInOccurrence(
                afterIntro.sequent().succedent().getFirst(), PosInTerm.getTopLevel(), false));
            assertEquals("q",
                afterApply.sequent().succedent().getFirst().formula().toString(),
                "simplification under the assumption p should yield q");

            // the soundness proof obligation p -> (((q & true) & p) <-> q) closes
            final Proof soundnessProof = lemma.getOrCreateSoundnessProof();
            new AutomaticProver().start(soundnessProof, 1000, 30000);
            assertTrue(soundnessProof.closed(), "soundness proof obligation did not close");

            // save and reload: both the introduction and the assumption-instantiated
            // taclet application replay
            final Path proofFile = Files.createTempFile("ossLemmaAssumes", ".proof");
            try {
                final String saveError = new ProofSaver(proof, proofFile).save();
                assertNull(saveError);
                final KeYEnvironment<DefaultUserInterfaceControl> reloadedEnv =
                    KeYEnvironment.load(proofFile);
                try {
                    final Proof reloaded = reloadedEnv.getLoadedProof();
                    assertNotNull(reloaded);
                    assertEquals(proof.countNodes(), reloaded.countNodes(),
                        "reloaded proof does not replay to the same size");
                } finally {
                    reloadedEnv.dispose();
                }
            } finally {
                Files.deleteIfExists(proofFile);
            }
        } finally {
            env.dispose();
        }
    }

    @Test
    public void testOssLemmaOnUpdateFormula() throws Exception {
        final KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment
                .load(TEST_CASE_DIRECTORY.resolve("lemmagen").resolve("ossLemma.key"));
        try {
            final Proof proof = env.getLoadedProof();
            assertNotNull(proof);
            OneStepSimplifier.refreshOSS(proof);

            // introduce the lemma at the top level succedent formula {i := 1}(i = 1)
            final Goal root = proof.openGoals().head();
            final SequentFormula sf = root.sequent().succedent().getFirst();
            final PosInOccurrence topLevel =
                new PosInOccurrence(sf, PosInTerm.getTopLevel(), false);
            assertTrue(OssLemmaIntroductionRule.INSTANCE.isApplicable(root, topLevel),
                "introduction rule not applicable - is the one step simplifier active?");
            root.apply(
                OssLemmaIntroductionRule.INSTANCE.createApp(topLevel, proof.getServices()));

            // exactly one lemma has been generated; it is a context-free equivalence rewrite
            final GeneratedLemmaRegistry registry = GeneratedLemmaRegistry.get(proof);
            assertEquals(1, registry.getLemmas().size());
            final GeneratedLemma lemma = registry.getLemmas().iterator().next();
            assertTrue(lemma.taclet().name().toString().startsWith("ossLemma_"),
                "content-hash name expected, got: " + lemma.taclet().name());
            assertTrue(lemma.taclet().assumesSequent().isEmpty(),
                "no replace-known steps involved, so the taclet must not have assumptions");
            assertNull(lemma.getSoundnessProofIfPresent());

            // apply the lemma: the formula becomes true
            final Goal afterIntro = proof.openGoals().head();
            final NoPosTacletApp lemmaApp =
                afterIntro.indexOfTaclets().lookup(lemma.taclet().name());
            assertNotNull(lemmaApp, "introduced taclet not found in goal-local taclet index");
            final PosInOccurrence applyPos = new PosInOccurrence(
                afterIntro.sequent().succedent().getFirst(), PosInTerm.getTopLevel(), false);
            final NoPosTacletApp matched = lemmaApp.matchFind(applyPos, proof.getServices());
            assertNotNull(matched, "generated taclet does not match its origin formula");
            final TacletApp positioned =
                matched.setPosInOccurrence(applyPos, proof.getServices());
            afterIntro.apply(positioned);

            final Goal afterApply = proof.openGoals().head();
            assertTrue(
                afterApply.sequent().succedent().getFirst().formula().op() == proof.getServices()
                        .getTermBuilder().tt().op(),
                "one step simplification of {i := 1}(i = 1) should yield true");

            // the soundness proof obligation (with updates) is created and closes
            final Proof soundnessProof = lemma.getOrCreateSoundnessProof();
            new AutomaticProver().start(soundnessProof, 1000, 30000);
            assertTrue(soundnessProof.closed(), "soundness proof obligation did not close");

            // save and reload: replaying the introduction re-runs the simplifier and
            // regenerates the taclet under the same content-derived name
            final Path proofFile = Files.createTempFile("ossLemma", ".proof");
            try {
                final String saveError = new ProofSaver(proof, proofFile).save();
                assertNull(saveError);
                final KeYEnvironment<DefaultUserInterfaceControl> reloadedEnv =
                    KeYEnvironment.load(proofFile);
                try {
                    final Proof reloaded = reloadedEnv.getLoadedProof();
                    assertNotNull(reloaded);
                    assertEquals(proof.countNodes(), reloaded.countNodes(),
                        "reloaded proof does not replay to the same size");
                } finally {
                    reloadedEnv.dispose();
                }
            } finally {
                Files.deleteIfExists(proofFile);
            }
        } finally {
            env.dispose();
        }
    }
}
