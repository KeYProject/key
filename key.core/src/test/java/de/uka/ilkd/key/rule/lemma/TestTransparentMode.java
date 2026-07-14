/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.taclettranslation.lemma.AutomaticProver;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for the {@code OSS_TRANSPARENT} strategy option ("mode 1"): automated proof search
 * performs aggregated simplifications of lemma-eligible formulas via generated lemma taclets
 * (introduction plus taclet application) instead of the opaque one step simplifier, which
 * remains responsible for formulas containing modal operators. The resulting proof saves and
 * replays.
 */
public class TestTransparentMode {

    private static final Path TEST_CASE_DIRECTORY = FindResources.getTestCasesDirectory();

    private static void setOssMode(Proof proof, String mode) {
        final StrategyProperties sp =
            proof.getSettings().getStrategySettings().getActiveStrategyProperties();
        sp.setProperty(StrategyProperties.OSS_OPTIONS_KEY, mode);
        proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
        // the active strategy caches its own property clone, so it must be renewed as well
        proof.setActiveStrategy(proof.getServices().getProfile()
                .getDefaultStrategyFactory().create(proof, sp));
        OneStepSimplifier.refreshOSS(proof);
    }

    private record Counts(int oss, int intro, int lemmaApps) {
    }

    private static Counts count(Proof proof) {
        int oss = 0;
        int intro = 0;
        int lemmaApps = 0;
        final var nodes = proof.root().subtreeIterator();
        while (nodes.hasNext()) {
            final Node node = nodes.next();
            if (node.getAppliedRuleApp() == null) {
                continue;
            }
            if (node.getAppliedRuleApp() instanceof OneStepSimplifierRuleApp) {
                oss++;
            } else if (node.getAppliedRuleApp().rule() == OssLemmaIntroductionRule.INSTANCE) {
                intro++;
            } else if (node.getAppliedRuleApp().rule().name().toString()
                    .startsWith("ossLemma_")) {
                lemmaApps++;
            }
        }
        return new Counts(oss, intro, lemmaApps);
    }

    @Test
    public void testTransparentAutomode() throws Exception {
        final Path file = TEST_CASE_DIRECTORY
                .resolve("../../../../../key.ui/examples/standard_key/arith/computation.key");
        assertTrue(Files.exists(file));

        try (KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(file)) {
            final Proof proof = env.getLoadedProof();
            assertNotNull(proof);
            setOssMode(proof, StrategyProperties.OSS_TRANSPARENT);

            new AutomaticProver().start(proof, 20000, 120000);
            assertTrue(proof.closed(), "automode in transparent mode did not close the proof");

            final Counts counts = count(proof);
            assertTrue(counts.intro() > 0,
                "transparent mode should introduce lemma taclets during search");
            // most introductions lead to an application; a few lemmas may be obsoleted by an
            // individual rule step rewriting the formula between introduction and application
            // (the individual rules compete with the lemma path since they remain available)
            assertTrue(counts.lemmaApps() > 0);
            assertTrue(counts.lemmaApps() <= counts.intro());
            assertTrue(counts.intro() - counts.lemmaApps() <= counts.intro() / 2,
                "too many introduced lemmas were never applied (intro=" + counts.intro()
                    + ", applied=" + counts.lemmaApps() + ")");
            // the opaque rule is never applied in transparent mode: formulas outside the lemma
            // fragment are simplified by the ordinary strategy in individual, visible steps
            assertEquals(0, counts.oss(),
                "no opaque simplifier application may occur in transparent mode");

            // the transparent proof saves and replays
            final Path proofFile = Files.createTempFile("transparentMode", ".proof");
            try {
                assertNull(new ProofSaver(proof, proofFile).save());
                try (KeYEnvironment<DefaultUserInterfaceControl> reloadedEnv =
                    KeYEnvironment.load(proofFile)) {
                    final Proof reloaded = reloadedEnv.getLoadedProof();
                    assertNotNull(reloaded);
                    assertEquals(proof.countNodes(), reloaded.countNodes(),
                        "transparent proof does not replay to the same size");
                    assertTrue(reloaded.closed());
                }
            } finally {
                Files.deleteIfExists(proofFile);
            }
        }
    }

    @Test
    public void testStockModeUnaffected() throws Exception {
        final Path file = TEST_CASE_DIRECTORY
                .resolve("../../../../../key.ui/examples/standard_key/arith/computation.key");
        try (KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(file)) {
            final Proof proof = env.getLoadedProof();
            assertNotNull(proof);
            setOssMode(proof, StrategyProperties.OSS_ON);

            new AutomaticProver().start(proof, 20000, 120000);
            assertTrue(proof.closed());

            final Counts counts = count(proof);
            assertTrue(counts.oss() > 0, "stock mode should still use the opaque simplifier");
            assertEquals(0, counts.intro(),
                "stock mode must not introduce lemma taclets automatically");
        }
    }
}
