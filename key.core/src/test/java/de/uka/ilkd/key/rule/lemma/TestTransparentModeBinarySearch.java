/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.taclettranslation.lemma.AutomaticProver;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Regression test for the BinarySearch failures in transparent mode: lemmas whose find and
 * assumes clauses share concrete bound variables (both stem from the same sequent) were rejected
 * by the taclet builder's bound-uniqueness check — a restriction that only makes sense for
 * schematic bound variables. That failure aborted automated search mid-run and made saving the
 * transparent proof impossible. Now: transparent automode closes the proof, the transparent form
 * saves and replays, and the lemma soundness obligations (including those with shared binders and
 * assumptions) are generated and discharged.
 */
public class TestTransparentModeBinarySearch {

    private static final Path TEST_CASE_DIRECTORY = FindResources.getTestCasesDirectory();

    @Test
    public void testTransparentBinarySearchEndToEnd() throws Exception {
        final Path file = TEST_CASE_DIRECTORY
                .resolve("../../../../../key.ui/examples/firstTouch/06-BinarySearch/project.key");
        assertTrue(Files.exists(file));

        try (KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(file)) {
            final Proof proof = env.getLoadedProof();
            assertNotNull(proof);
            final StrategyProperties sp =
                proof.getSettings().getStrategySettings().getActiveStrategyProperties();
            sp.setProperty(StrategyProperties.OSS_OPTIONS_KEY,
                StrategyProperties.OSS_TRANSPARENT);
            proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
            proof.setActiveStrategy(proof.getServices().getProfile()
                    .getDefaultStrategyFactory().create(proof, sp));
            OneStepSimplifier.refreshOSS(proof);

            new AutomaticProver().start(proof, 30000, 300000);
            assertTrue(proof.closed(),
                "transparent automode did not close BinarySearch (previously aborted by the"
                    + " bound-uniqueness check)");

            final GeneratedLemmaRegistry registry = GeneratedLemmaRegistry.get(proof);
            assertFalse(registry.getLemmas().isEmpty());

            // the transparent form saves (previously failed with a TacletBuilderException)
            // and replays to closed
            final Path tmpDir = Files.createDirectories(Path.of("build", "tmp", "lemmaTests"));
            final Path outFile =
                Files.createTempFile(tmpDir, "binarySearchTransparent", ".proof");
            try {
                // the proof is already transparent, so nothing is left to elaborate; saving is
                // a faithful copy whose replay re-introduces the lemmas (this used to fail with
                // the taclet builder's bound-uniqueness check)
                TransparentProofSaver.save(proof, outFile);
                try (KeYEnvironment<DefaultUserInterfaceControl> reloadedEnv =
                    KeYEnvironment.load(outFile)) {
                    final Proof reloaded = reloadedEnv.getLoadedProof();
                    assertNotNull(reloaded);
                    assertTrue(reloaded.closed(),
                        "saved transparent BinarySearch proof did not replay to closed");
                    int intros = 0;
                    final var nodes = reloaded.root().subtreeIterator();
                    while (nodes.hasNext()) {
                        final var app = nodes.next().getAppliedRuleApp();
                        if (app != null && app.rule() instanceof OssLemmaIntroductionRule) {
                            intros++;
                        }
                    }
                    assertTrue(intros > 0,
                        "reloaded transparent proof should contain lemma introductions");
                }
            } finally {
                Files.deleteIfExists(outFile);
            }

            // all lemma soundness obligations generate; count how many close in the base
            // calculus within the bound (the batch must be robust and must not throw)
            final LemmaProver.Result result =
                LemmaProver.proveAll(registry.getLemmas(), 10000, null);
            assertTrue(result.remaining().isEmpty(),
                "lemma obligations did not close: " + result.remaining().stream()
                        .map(l -> l.taclet().name().toString()).toList());
        }
    }
}
