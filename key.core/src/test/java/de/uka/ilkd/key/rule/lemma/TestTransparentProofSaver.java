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
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.taclettranslation.lemma.AutomaticProver;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Test for {@link TransparentProofSaver}: a proof found with the opaque one step simplifier is
 * saved in its transparent form; the saved file loads, replays, is closed, and contains lemma
 * introductions instead of the eligible opaque steps. The original proof is unchanged.
 */
public class TestTransparentProofSaver {

    private static final Path TEST_CASE_DIRECTORY = FindResources.getTestCasesDirectory();

    @Test
    public void testSaveTransparentAndReload() throws Exception {
        final Path file = TEST_CASE_DIRECTORY
                .resolve("../../../../../key.ui/examples/standard_key/arith/computation.key");
        assertTrue(Files.exists(file));

        try (KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(file)) {
            final Proof proof = env.getLoadedProof();
            assertNotNull(proof);
            final StrategyProperties sp =
                proof.getSettings().getStrategySettings().getActiveStrategyProperties();
            sp.setProperty(StrategyProperties.OSS_OPTIONS_KEY, StrategyProperties.OSS_ON);
            proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
            OneStepSimplifier.refreshOSS(proof);

            new AutomaticProver().start(proof, 20000, 120000);
            assertTrue(proof.closed());
            final int originalNodes = proof.countNodes();

            final Path outFile = Files.createTempFile("transparent", ".proof");
            try {
                final TransparentProofSaver.Result result =
                    TransparentProofSaver.save(proof, outFile);
                assertTrue(result.elaborated() > 0, "nothing was elaborated");
                assertTrue(result.lemmas() > 0);

                // the original proof is untouched
                assertEquals(originalNodes, proof.countNodes());
                assertTrue(proof.closed());

                // the saved transparent proof loads, replays, and is closed
                try (KeYEnvironment<DefaultUserInterfaceControl> reloadedEnv =
                    KeYEnvironment.load(outFile)) {
                    final Proof reloaded = reloadedEnv.getLoadedProof();
                    assertNotNull(reloaded);
                    assertTrue(reloaded.closed(), "transparent proof did not replay to closed");
                    assertEquals(originalNodes + result.elaborated(), reloaded.countNodes());

                    int intros = 0;
                    int oss = 0;
                    final var nodes = reloaded.root().subtreeIterator();
                    while (nodes.hasNext()) {
                        final Node node = nodes.next();
                        if (node.getAppliedRuleApp() == null) {
                            continue;
                        }
                        if (node.getAppliedRuleApp()
                                .rule() instanceof OssLemmaIntroductionRule) {
                            intros++;
                        } else if (node
                                .getAppliedRuleApp() instanceof OneStepSimplifierRuleApp) {
                            oss++;
                        }
                    }
                    assertEquals(result.elaborated(), intros);
                    assertEquals(result.copiedOss(), oss);
                }
            } finally {
                Files.deleteIfExists(outFile);
            }
        }
    }
}
