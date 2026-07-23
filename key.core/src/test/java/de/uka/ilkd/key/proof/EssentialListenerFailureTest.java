/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.util.HelperClassForTests;
import de.uka.ilkd.key.util.ProofStarter;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Pins the failure semantics of {@link EssentialProofListener}s (in contrast to the non-essential
 * listener isolation tested by {@code ProofListenerIsolationTest}): when an essential listener
 * fails, the proof search must STOP (the step may have left the proof inconsistent), the proof is
 * marked {@linkplain Proof#isErroneous() erroneous} so that no new search can be started, but the
 * proof can still be saved for a later reload attempt.
 */
public class EssentialListenerFailureTest {

    /** A rule-app listener that is part of the proving machinery and always fails. */
    private static final class RogueEssentialListener
            implements RuleAppListener, EssentialProofListener {
        int calls = 0;

        @Override
        public void ruleApplied(ProofEvent e) {
            calls++;
            throw new IllegalStateException("boom from an essential proof listener");
        }
    }

    @Test
    public void essentialListenerFailureStopsSearchMarksErroneousButAllowsSaving()
            throws Exception {
        final Path key = HelperClassForTests.TESTCASE_DIRECTORY.resolve("naming")
                .resolve("skolemSiblings.key");
        final KeYEnvironment<?> env = KeYEnvironment.load(JavaProfile.getDefaultInstance(),
            key, null, null, null, true);
        try {
            final Proof proof = env.getLoadedProof();
            final RogueEssentialListener rogue = new RogueEssentialListener();
            proof.addRuleAppListener(rogue);

            // run automode: the first applied rule fires the listener, which fails
            final ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            starter.setMaxRuleApplications(50);
            starter.start();

            // the failure marks the proof erroneous and stops the search after that step
            assertTrue(proof.isErroneous(),
                "an essential listener failure must mark the proof erroneous");
            assertEquals(1, rogue.calls,
                "the search must stop after the step whose notification failed");
            final int nodesAfterStop = proof.countNodes();

            // the listener is NOT silently unregistered and no new search can be started:
            // a second automode run must not apply any further rules
            final ProofStarter again = new ProofStarter(false);
            again.init(proof);
            again.setMaxRuleApplications(50);
            again.start();
            assertEquals(nodesAfterStop, proof.countNodes(),
                "no new proof search may run on an erroneous proof");

            // ... but the proof can still be saved (for a later reload attempt)
            final Path out = Files.createTempFile("erroneousProof", ".proof");
            try {
                final String saveResult = new ProofSaver(proof, out).save();
                assertNull(saveResult, "saving an erroneous proof must still work: " + saveResult);
                assertTrue(Files.size(out) > 0, "saved proof file must not be empty");
            } finally {
                Files.deleteIfExists(out);
            }
        } finally {
            env.dispose();
        }
    }
}
