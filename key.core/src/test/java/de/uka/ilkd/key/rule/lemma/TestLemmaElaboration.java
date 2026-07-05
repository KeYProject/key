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
 * End-to-end test for {@link LemmaElaboratingProofReplayer} ("mode 2"): a proof is found with
 * the fast opaque one step simplifier, then elaborated onto a fresh proof in which every
 * lemma-eligible simplifier application is replaced by taclet introduction plus taclet
 * application; non-eligible applications (modal operators) are copied unchanged. The elaborated
 * proof closes, and all generated lemmas are certified by discharging their soundness proof
 * obligations.
 */
public class TestLemmaElaboration {

    private static final Path TEST_CASE_DIRECTORY = FindResources.getTestCasesDirectory();

    private static void activateOss(Proof proof) {
        final StrategyProperties sp =
            proof.getSettings().getStrategySettings().getActiveStrategyProperties();
        sp.setProperty(StrategyProperties.OSS_OPTIONS_KEY, StrategyProperties.OSS_ON);
        proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
        OneStepSimplifier.refreshOSS(proof);
    }

    private static int countOssApps(Proof proof) {
        int count = 0;
        final var nodes = proof.root().subtreeIterator();
        while (nodes.hasNext()) {
            if (nodes.next().getAppliedRuleApp() instanceof OneStepSimplifierRuleApp) {
                count++;
            }
        }
        return count;
    }

    private static int countIntroApps(Proof proof) {
        int count = 0;
        final var nodes = proof.root().subtreeIterator();
        while (nodes.hasNext()) {
            final Node node = nodes.next();
            if (node.getAppliedRuleApp() != null
                    && node.getAppliedRuleApp().rule() == OssLemmaIntroductionRule.INSTANCE) {
                count++;
            }
        }
        return count;
    }

    @Test
    public void testElaborateComputationProof() throws Exception {
        final Path file = TEST_CASE_DIRECTORY
                .resolve("../../../../../key.ui/examples/standard_key/arith/computation.key");
        assertTrue(Files.exists(file), "example problem not found: " + file);

        try (KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(file);
                KeYEnvironment<DefaultUserInterfaceControl> targetEnv =
                    KeYEnvironment.load(file)) {

            // find the proof with the fast opaque simplifier
            final Proof original = env.getLoadedProof();
            assertNotNull(original);
            activateOss(original);
            new AutomaticProver().start(original, 20000, 120000);
            assertTrue(original.closed(), "automode did not close the original proof");
            final int originalOssApps = countOssApps(original);
            assertTrue(originalOssApps > 0,
                "test problem should exercise the one step simplifier");

            // elaborate onto a fresh proof of the same problem
            final Proof target = targetEnv.getLoadedProof();
            assertNotNull(target);
            activateOss(target);
            final LemmaElaboratingProofReplayer replayer =
                LemmaElaboratingProofReplayer.elaborate(original, target);

            assertTrue(target.closed(), "elaborated proof did not close");
            assertTrue(replayer.getElaboratedCount() > 0,
                "no simplifier application was elaborated");
            assertEquals(originalOssApps,
                replayer.getElaboratedCount() + replayer.getCopiedOssCount(),
                "every original simplifier application is either elaborated or copied");
            assertEquals(replayer.getCopiedOssCount(), countOssApps(target),
                "only non-eligible simplifier applications remain in the elaborated proof");
            assertEquals(replayer.getElaboratedCount(), countIntroApps(target),
                "each elaborated application contributes one introduction step");
            assertEquals(original.countNodes() + replayer.getElaboratedCount(),
                target.countNodes(),
                "each elaborated application adds exactly one node");

            // certify: every generated lemma's soundness proof obligation closes
            final GeneratedLemmaRegistry registry = GeneratedLemmaRegistry.get(target);
            System.out.printf(
                "ELABORATION: ossApps=%d elaborated=%d copied=%d distinctLemmas=%d "
                    + "nodes %d -> %d%n",
                originalOssApps, replayer.getElaboratedCount(), replayer.getCopiedOssCount(),
                registry.getLemmas().size(), original.countNodes(), target.countNodes());
            assertFalse(registry.getLemmas().isEmpty());
            assertTrue(registry.getLemmas().size() <= replayer.getElaboratedCount(),
                "reuse: at most one lemma per elaborated application");
            for (final GeneratedLemma lemma : registry.getLemmas()) {
                final Proof po = lemma.getOrCreateSoundnessProof();
                new AutomaticProver().start(po, 10000, 60000);
                assertTrue(po.closed(),
                    "soundness proof obligation of " + lemma.taclet().name()
                        + " did not close");
            }
        }
    }
}
