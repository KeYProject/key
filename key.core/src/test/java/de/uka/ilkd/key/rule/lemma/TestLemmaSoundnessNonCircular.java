/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import java.nio.file.Path;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.taclettranslation.lemma.AutomaticProver;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Guards the soundness of generated lemmas against circular justification: even when the main
 * proof runs the one step simplifier in transparent mode, a lemma's soundness proof obligation
 * must be discharged in the base calculus (opaque simplifier), never by generating and applying
 * further lemmas — which would re-derive the very simplification the obligation is meant to
 * justify, and never terminate.
 */
public class TestLemmaSoundnessNonCircular {

    private static final Path TEST_CASE_DIRECTORY = FindResources.getTestCasesDirectory();

    @Test
    public void testSoundnessProofUsesBaseCalculus() throws Exception {
        final Path file = TEST_CASE_DIRECTORY
                .resolve("../../../../../key.ui/examples/standard_key/arith/computation.key");

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
            new AutomaticProver().start(proof, 20000, 120000);
            assertTrue(proof.closed());

            final GeneratedLemmaRegistry registry = GeneratedLemmaRegistry.get(proof);
            assertFalse(registry.getMissingLemmas().isEmpty());

            for (final GeneratedLemma lemma : registry.getMissingLemmas()) {
                final Proof po = lemma.getOrCreateSoundnessProof();

                // the soundness proof runs in the base calculus with the one step simplifier
                // switched off entirely (not even its opaque mode, which would close the
                // obligation by the very aggregated simplification under scrutiny)
                assertEquals(StrategyProperties.OSS_OFF,
                    po.getSettings().getStrategySettings().getActiveStrategyProperties()
                            .getProperty(StrategyProperties.OSS_OPTIONS_KEY),
                    "the soundness proof of " + lemma.taclet().name()
                        + " must run with the one step simplifier disabled");

                new AutomaticProver().start(po, 10000, 60000);
                assertTrue(po.closed(),
                    "soundness proof of " + lemma.taclet().name() + " did not close");

                // it must not contain any lemma introduction or application (no circularity)
                final var nodes = po.root().subtreeIterator();
                while (nodes.hasNext()) {
                    final Node node = nodes.next();
                    final var app = node.getAppliedRuleApp();
                    if (app == null) {
                        continue;
                    }
                    final String ruleName = app.rule().name().toString();
                    assertFalse(ruleName.startsWith("introduce_ossLemma"),
                        "soundness proof of " + lemma.taclet().name()
                            + " introduces a lemma (circular)");
                    assertFalse(ruleName.startsWith("ossLemma_"),
                        "soundness proof of " + lemma.taclet().name()
                            + " applies a generated lemma (circular): " + ruleName);
                }
            }
        }
    }
}
