/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.replay;

import java.lang.reflect.Field;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.HashSet;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Counter;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests for {@link CopyingProofReplayer}.
 *
 * @author Arne Keller
 */
class TestCopyingReplayer {
    public static final Path testCaseDirectory = FindResources.getTestCasesDirectory();

    /**
     * Reset all counters associated with this service.
     * Only use this method if the proof is empty!
     */
    public void resetCounters(Proof proof) {
        if (proof.root().childrenCount() > 0) {
            throw new IllegalStateException("tried to reset counters on non-empty proof");
        }

        try {
            final Field countersField =
                HelperClassForTests.getPrivateField(proof.getServices(), "counters");
            // noinspection unchecked
            ((HashMap<String, Counter>) countersField.get(proof.getServices())).clear();
        } catch (NoSuchFieldException | IllegalAccessException e) {
            throw new RuntimeException(e);
        }
    }

    @Test
    void testJavaProof() throws Exception {
        GeneralSettings.noPruningClosed = false;

        final var file = testCaseDirectory.resolve(
            "../../../../../key.ui/examples/heap/verifyThis15_1_RelaxedPrefix/relax.proof");
        assertTrue(Files.exists(file));

        try (var env = KeYEnvironment.load(file);
                var env2 = KeYEnvironment.load(file)) {
            assertNotNull(env.getLoadedProof());
            assertTrue(env.getLoadedProof().closed());

            assertNotNull(env2.getLoadedProof());
            assertTrue(env2.getLoadedProof().closed());

            Proof proof1 = env.getLoadedProof();
            Proof proof2 = env2.getLoadedProof();

            // clear proof2, replay proof1 on top
            proof2.pruneProof(proof2.root());
            resetCounters(proof2);
            new CopyingProofReplayer(proof1, proof2).copy(proof1.root(),
                proof2.getOpenGoal(proof2.root()), new HashSet<>());

            assertTrue(proof2.closed());
            Assertions.assertEquals(proof1.countNodes(), proof2.countNodes());

            GeneralSettings.noPruningClosed = true;
        }
    }
}
