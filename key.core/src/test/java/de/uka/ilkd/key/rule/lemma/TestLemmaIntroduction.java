/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.taclettranslation.lemma.AutomaticProver;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * End-to-end test for the taclet-generating transformer approach on the toy
 * {@link AddLiteralsLemmaGenerator}: introduction of the generated taclet, its application, the
 * soundness proof obligation, proof save/reload (replay), and reuse of the taclet after pruning.
 */
public class TestLemmaIntroduction {

    private static final Path TEST_CASE_DIRECTORY = FindResources.getTestCasesDirectory();

    private static PosInOccurrence firstSuccedentSubTerm(Goal goal, int subTerm) {
        final SequentFormula sf = goal.sequent().succedent().getFirst();
        return new PosInOccurrence(sf, PosInTerm.getTopLevel().down(subTerm), false);
    }

    @Test
    public void testIntroduceApplyProveReloadAndReuse() throws Exception {
        final KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment
                .load(TEST_CASE_DIRECTORY.resolve("lemmagen").resolve("addLiterals.key"));
        try {
            final Proof proof = env.getLoadedProof();
            assertNotNull(proof);

            // step 1: introduce the lemma taclet at "5 + 7" (left of the equality)
            final Goal root = proof.openGoals().head();
            final PosInOccurrence addPos = firstSuccedentSubTerm(root, 0);
            assertTrue(AddLiteralsLemmaIntroductionRule.INSTANCE.isApplicable(root, addPos));
            root.apply(AddLiteralsLemmaIntroductionRule.INSTANCE.createApp(addPos,
                proof.getServices()));

            final Name lemmaName = MiscTools.toValidTacletName("addLitLemma_5_7");
            final Goal afterIntro = proof.openGoals().head();
            final NoPosTacletApp lemmaApp = afterIntro.indexOfTaclets().lookup(lemmaName);
            assertNotNull(lemmaApp, "introduced taclet not found in goal-local taclet index");

            // the taclet is justified as a generated lemma, not as an axiom
            final RuleJustification justification =
                proof.getInitConfig().getJustifInfo().getJustification(lemmaApp.taclet());
            assertInstanceOf(GeneratedLemmaJustification.class, justification);
            assertFalse(justification.isAxiomJustification());

            // step 2: apply the lemma; "5 + 7 = 12" becomes "12 = 12"
            final PosInOccurrence applyPos = firstSuccedentSubTerm(afterIntro, 0);
            final NoPosTacletApp matched =
                lemmaApp.matchFind(applyPos, proof.getServices());
            assertNotNull(matched, "generated taclet does not match its origin term");
            final TacletApp positioned =
                matched.setPosInOccurrence(applyPos, proof.getServices());
            afterIntro.apply(positioned);

            final Goal afterApply = proof.openGoals().head();
            final JTerm equality =
                (JTerm) afterApply.sequent().succedent().getFirst().formula();
            assertEquals(equality.sub(1), equality.sub(0),
                "lemma application should fold 5 + 7 to the literal 12");

            // the soundness proof obligation exists and is provable
            final GeneratedLemma lemma = GeneratedLemmaRegistry.get(proof).lookup(lemmaName);
            assertNotNull(lemma);
            final Proof soundnessProof = lemma.soundnessProof();
            assertNotNull(soundnessProof);
            new AutomaticProver().start(soundnessProof, 1000, 30000);
            assertTrue(soundnessProof.closed(), "soundness proof obligation did not close");

            // save and reload: replaying the introduction regenerates the taclet, the recorded
            // taclet application resolves against it by name
            final Path proofFile = Files.createTempFile("addLitLemma", ".proof");
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

            // prune to the root and re-introduce: the identical taclet instance is reused,
            // no second justification or proof obligation is created
            proof.pruneProof(proof.root());
            final Goal pruned = proof.openGoals().head();
            pruned.apply(AddLiteralsLemmaIntroductionRule.INSTANCE.createApp(
                firstSuccedentSubTerm(pruned, 0), proof.getServices()));
            final NoPosTacletApp reintroduced =
                proof.openGoals().head().indexOfTaclets().lookup(lemmaName);
            assertNotNull(reintroduced);
            assertSame(lemma.taclet(), reintroduced.taclet(),
                "re-introduction after pruning must reuse the cached taclet instance");
            assertEquals(1, GeneratedLemmaRegistry.get(proof).getLemmas().size());
        } finally {
            env.dispose();
        }
    }
}
