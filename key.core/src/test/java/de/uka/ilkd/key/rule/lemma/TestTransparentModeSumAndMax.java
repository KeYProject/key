/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.taclettranslation.lemma.AutomaticProver;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;
import static org.junit.jupiter.api.Assertions.*;

/**
 * Regression test for transparent mode on a heap/symbolic-execution scale proof (SumAndMax).
 * Guards against two automation defects observed on this example:
 * <ul>
 * <li>dead re-introductions: formulas on sibling branches that are equal in their printed form
 * but contain distinct proof-local symbol instances aliased to the same lemma, producing taclets
 * that never match and an endless stream of introduction steps (fixed by qualifying lemma names
 * with the replay-stable introduction-node id);</li>
 * <li>no-op lemmas whose find and replacewith differ only in term labels or bound variable
 * names (rejected by the generator).</li>
 * </ul>
 */
public class TestTransparentModeSumAndMax {

    private static final Path TEST_CASE_DIRECTORY = FindResources.getTestCasesDirectory();

    @Test
    public void testTransparentAutomodeClosesSumAndMax() throws Exception {
        final Path file = TEST_CASE_DIRECTORY.resolve(
            "../../../../../key.ui/examples/heap/vstte10_01_SumAndMax/SumAndMax_sumAndMax.key");
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

            new AutomaticProver().start(proof, 12000, 300000);
            assertTrue(proof.closed(), "transparent automode did not close SumAndMax");

            int intro = 0;
            int lemmaApps = 0;
            final var nodes = proof.root().subtreeIterator();
            while (nodes.hasNext()) {
                final Node node = nodes.next();
                final var app = node.getAppliedRuleApp();
                if (app == null) {
                    continue;
                }
                if (app.rule() == OssLemmaIntroductionRule.INSTANCE) {
                    intro++;
                } else if (app instanceof OneStepSimplifierRuleApp) {
                    fail("no opaque simplifier application may occur in transparent mode");
                } else if (app.rule().name().toString().startsWith("ossLemma_")) {
                    lemmaApps++;
                    final RewriteTaclet taclet = (RewriteTaclet) app.rule();
                    final JTerm find = (JTerm) taclet.find();
                    final JTerm replaceWith = (JTerm) ((RewriteTacletGoalTemplate) taclet
                            .goalTemplates().head()).replaceWith();
                    assertFalse(
                        RENAMING_TERM_PROPERTY.equalsModThisProperty(find, replaceWith),
                        "no-op lemma applied: " + taclet.name());
                }
            }

            final GeneratedLemmaRegistry registry = GeneratedLemmaRegistry.get(proof);
            assertTrue(intro > 0);
            assertEquals(intro, registry.getLemmas().size(),
                "every introduction must mint a fresh lemma - a mismatch means dead"
                    + " re-introductions of aliased lemmas");
            assertTrue(intro - lemmaApps <= intro / 4,
                "most introduced lemmas should actually be applied (intro=" + intro
                    + ", applied=" + lemmaApps + ")");

            // the introduction-node-qualified names must be replay-stable. The proof is saved
            // inside the build tree: the problem has a boot classpath below the checkout, and
            // the saver relativizes paths against the save location.
            final Path tmpDir = Files.createDirectories(Path.of("build", "tmp", "lemmaTests"));
            final Path proofFile =
                Files.createTempFile(tmpDir, "sumAndMaxTransparent", ".proof");
            try {
                assertNull(new ProofSaver(proof, proofFile).save());
                try (KeYEnvironment<DefaultUserInterfaceControl> reloadedEnv =
                    KeYEnvironment.load(proofFile)) {
                    final Proof reloaded = reloadedEnv.getLoadedProof();
                    assertNotNull(reloaded);
                    if (!reloaded.closed() && reloadedEnv.getReplayResult() != null) {
                        // diagnostics on failure only
                        reloadedEnv.getReplayResult().getErrorList().stream().limit(3)
                                .forEach(t -> System.err.println("replay error: " + t
                                    + (t.getCause() != null ? " caused by " + t.getCause()
                                            : "")));
                    }
                    assertTrue(reloaded.closed(),
                        "reloaded transparent SumAndMax proof did not replay to closed");
                    assertEquals(proof.countNodes(), reloaded.countNodes());
                }
            } finally {
                Files.deleteIfExists(proofFile);
            }
        }
    }
}
