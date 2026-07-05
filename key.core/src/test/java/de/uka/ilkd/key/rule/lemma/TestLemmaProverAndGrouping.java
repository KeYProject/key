/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.taclettranslation.lemma.AutomaticProver;

import org.key_project.logic.Name;
import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests the batch proving and content grouping that back the redesigned lemma dependency view:
 * generated lemmas are grouped by generator and by content, and their soundness obligations are
 * discharged in a bounded batch, with those that do not close reported for manual completion.
 */
public class TestLemmaProverAndGrouping {

    private static final Path TEST_CASE_DIRECTORY = FindResources.getTestCasesDirectory();

    private static Proof transparentClosedSumAndMax(
            KeYEnvironment<DefaultUserInterfaceControl> env) throws Exception {
        final Proof proof = env.getLoadedProof();
        assertNotNull(proof);
        final StrategyProperties sp =
            proof.getSettings().getStrategySettings().getActiveStrategyProperties();
        sp.setProperty(StrategyProperties.OSS_OPTIONS_KEY, StrategyProperties.OSS_TRANSPARENT);
        proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
        proof.setActiveStrategy(
            proof.getServices().getProfile().getDefaultStrategyFactory().create(proof, sp));
        OneStepSimplifier.refreshOSS(proof);
        new AutomaticProver().start(proof, 20000, 300000);
        assertTrue(proof.closed());
        return proof;
    }

    private static Proof transparentClosed(KeYEnvironment<DefaultUserInterfaceControl> env,
            int maxSteps) throws Exception {
        final Proof proof = env.getLoadedProof();
        assertNotNull(proof);
        final StrategyProperties sp =
            proof.getSettings().getStrategySettings().getActiveStrategyProperties();
        sp.setProperty(StrategyProperties.OSS_OPTIONS_KEY, StrategyProperties.OSS_TRANSPARENT);
        proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
        proof.setActiveStrategy(
            proof.getServices().getProfile().getDefaultStrategyFactory().create(proof, sp));
        OneStepSimplifier.refreshOSS(proof);
        new AutomaticProver().start(proof, maxSteps, 300000);
        assertTrue(proof.closed());
        return proof;
    }

    @Test
    public void testQuantifierLemmaObligationsGenerateAndClose() throws Exception {
        // Regression for the DefaultLemmaGenerator bug: taclets whose find/replacewith contain
        // concrete (non-schematic) quantifiers were rebuilt with an empty bound-variable list and
        // failed the term arity check during proof-obligation generation. SumAndMax generates
        // such lemmas. Their obligations must now both generate and close in the base calculus.
        final Path file = TEST_CASE_DIRECTORY.resolve(
            "../../../../../key.ui/examples/heap/vstte10_01_SumAndMax/SumAndMax_sumAndMax.key");

        try (KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(file)) {
            final Proof proof = transparentClosedSumAndMax(env);
            final GeneratedLemmaRegistry registry = GeneratedLemmaRegistry.get(proof);

            int quantifierLemmas = 0;
            for (final GeneratedLemma lemma : registry.getLemmas()) {
                if (!containsQuantifier((de.uka.ilkd.key.logic.JTerm) lemma.taclet().find())) {
                    continue;
                }
                quantifierLemmas++;
                // generation must not throw (the bug), and the obligation must close
                final Proof po = lemma.getOrCreateSoundnessProof();
                new AutomaticProver().start(po, 12000, 120000);
                assertTrue(po.closed(),
                    "quantifier lemma obligation did not close: " + lemma.taclet().name());
                if (quantifierLemmas >= 3) {
                    break; // a few are enough for a regression guard
                }
            }
            assertTrue(quantifierLemmas > 0,
                "SumAndMax should generate lemmas containing quantifiers");
        }
    }

    private static boolean containsQuantifier(de.uka.ilkd.key.logic.JTerm t) {
        if (t.op() instanceof de.uka.ilkd.key.logic.op.Quantifier) {
            return true;
        }
        for (int i = 0; i < t.arity(); i++) {
            if (containsQuantifier(t.sub(i))) {
                return true;
            }
        }
        return false;
    }

    @Test
    public void testContentGroupingCollapsesDuplicates() throws Exception {
        // SumAndMax generates many introduction-point-distinct lemmas that denote the same
        // simplifications: content grouping must collapse them.
        final Path file = TEST_CASE_DIRECTORY.resolve(
            "../../../../../key.ui/examples/heap/vstte10_01_SumAndMax/SumAndMax_sumAndMax.key");

        try (KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(file)) {
            final Proof proof = transparentClosedSumAndMax(env);
            final GeneratedLemmaRegistry registry = GeneratedLemmaRegistry.get(proof);

            final Map<Name, List<GeneratedLemma>> byGenerator = registry.getLemmasByGenerator();
            assertEquals(1, byGenerator.size(), "all lemmas come from the OSS generator");
            final List<GeneratedLemma> ossLemmas =
                byGenerator.get(OssLemmaGenerator.INSTANCE.name());
            assertNotNull(ossLemmas);
            assertEquals(registry.getLemmas().size(), ossLemmas.size());

            final Map<String, List<GeneratedLemma>> byContent =
                GeneratedLemmaRegistry.groupByContent(ossLemmas);
            assertTrue(byContent.size() < ossLemmas.size(),
                "content grouping should collapse duplicate simplifications (" + ossLemmas.size()
                    + " lemmas, " + byContent.size() + " distinct)");
            assertEquals(ossLemmas.size(),
                byContent.values().stream().mapToInt(List::size).sum());
        }
    }

    @Test
    public void testBatchProvingDischargesAndSaves() throws Exception {
        final Path file = TEST_CASE_DIRECTORY
                .resolve("../../../../../key.ui/examples/standard_key/arith/computation.key");

        try (KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(file)) {
            final Proof proof = transparentClosed(env, 20000);
            final GeneratedLemmaRegistry registry = GeneratedLemmaRegistry.get(proof);
            final List<GeneratedLemma> lemmas =
                registry.getMissingLemmas();
            assertFalse(lemmas.isEmpty());

            final Path saveDir =
                Files.createDirectories(Path.of("build", "tmp", "lemmaProverTest"));
            final LemmaProver.Result result = LemmaProver.proveAll(lemmas, 10000, saveDir);

            assertEquals(lemmas.size(), result.proven().size() + result.remaining().size());
            assertFalse(result.proven().isEmpty(), "arith lemmas should close");
            for (final GeneratedLemma lemma : result.proven()) {
                assertTrue(lemma.isProven());
                assertSame(proof.getEnv(), lemma.getSoundnessProofIfPresent().getEnv(),
                    "obligation proof lives in the main proof's environment");
            }
            assertTrue(registry.getMissingLemmas().size() <= result.remaining().size(),
                "proven lemmas leave the missing set");
            assertEquals(lemmas.size(), result.saved(), "each obligation proof was saved");
            for (final GeneratedLemma lemma : lemmas) {
                final Path expected = saveDir.resolve(
                    de.uka.ilkd.key.util.MiscTools.toValidFileName(
                        lemma.taclet().name().toString()) + ".proof");
                assertTrue(Files.exists(expected), "missing saved proof: " + expected);
                Files.deleteIfExists(expected);
            }
        }
    }
}
