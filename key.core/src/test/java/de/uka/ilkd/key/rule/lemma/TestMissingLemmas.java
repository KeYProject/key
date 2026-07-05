/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import java.nio.file.Path;
import java.util.List;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.taclettranslation.lemma.AutomaticProver;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests the "missing lemmas" bookkeeping that backs the Missing Lemmas tab of the proof
 * management dialog: after a proof is elaborated (or found in transparent mode) it depends on
 * generated lemmas whose soundness proof obligations are initially missing; creating and
 * discharging those obligations removes them from the missing set and registers them in the
 * proof environment.
 */
public class TestMissingLemmas {

    private static final Path TEST_CASE_DIRECTORY = FindResources.getTestCasesDirectory();

    @Test
    public void testMissingLemmasLifecycle() throws Exception {
        final Path file = TEST_CASE_DIRECTORY
                .resolve("../../../../../key.ui/examples/standard_key/arith/computation.key");

        try (KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(file);
                KeYEnvironment<DefaultUserInterfaceControl> targetEnv =
                    KeYEnvironment.load(file)) {

            final Proof original = env.getLoadedProof();
            assertNotNull(original);
            final StrategyProperties sp =
                original.getSettings().getStrategySettings().getActiveStrategyProperties();
            sp.setProperty(StrategyProperties.OSS_OPTIONS_KEY, StrategyProperties.OSS_ON);
            original.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
            OneStepSimplifier.refreshOSS(original);
            new AutomaticProver().start(original, 20000, 120000);
            assertTrue(original.closed());

            final Proof target = targetEnv.getLoadedProof();
            assertNotNull(target);
            OneStepSimplifier.refreshOSS(target);
            final LemmaElaboratingProofReplayer replayer =
                LemmaElaboratingProofReplayer.elaborate(original, target);
            assertTrue(target.closed());
            assertTrue(replayer.getElaboratedCount() > 0);

            final GeneratedLemmaRegistry registry = GeneratedLemmaRegistry.get(target);

            // initially every generated lemma is missing (no soundness proof created yet)
            final List<GeneratedLemma> missing = registry.getMissingLemmas();
            assertEquals(registry.getLemmas().size(), missing.size(),
                "all generated lemmas are initially missing");
            assertFalse(missing.isEmpty());

            // creating the obligation alone does not register it (a batch of closed obligations
            // must not flood the environment)
            final GeneratedLemma first = missing.get(0);
            assertFalse(first.isSoundnessProofPresent());
            first.getOrCreateSoundnessProofAggregate();
            assertTrue(first.isSoundnessProofPresent());
            assertFalse(target.getEnv().getProofs().stream()
                    .anyMatch(pl -> pl.getFirstProof() == first.getSoundnessProofIfPresent()),
                "creating the obligation must not register it in the environment");

            // "load as side proof": registering surfaces it in the environment
            final ProofAggregate aggregate = first.registerInEnvironment();
            final Proof soundnessProof = aggregate.getFirstProof();
            assertSame(target.getEnv(), soundnessProof.getEnv(),
                "registered soundness proof lives in the main proof's environment");
            assertTrue(target.getEnv().getProofs().stream()
                    .anyMatch(pl -> pl.getFirstProof() == soundnessProof),
                "registered soundness proof must be in the proof environment");
            // registering again does not duplicate it
            first.registerInEnvironment();
            assertEquals(1, target.getEnv().getProofs().stream()
                    .filter(pl -> pl.getFirstProof() == soundnessProof).count());

            // an open (not yet closed) soundness proof still counts as missing
            assertTrue(registry.getMissingLemmas().contains(first),
                "an unclosed soundness proof leaves the lemma in the missing set");

            // discharge it: the lemma leaves the missing set
            new AutomaticProver().start(soundnessProof, 10000, 60000);
            assertTrue(soundnessProof.closed());
            assertTrue(first.isProven());
            assertFalse(registry.getMissingLemmas().contains(first),
                "a proven lemma is no longer missing");
            assertEquals(missing.size() - 1, registry.getMissingLemmas().size());

            // requesting the aggregate again returns the same proof (no duplicate side proof)
            assertSame(soundnessProof, first.getOrCreateSoundnessProofAggregate().getFirstProof());
        }
    }
}
