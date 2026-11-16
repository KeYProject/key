/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.replay;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Objects;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Counter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
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
    public static final Path testCaseDirectory = Objects
            .requireNonNull(FindResources.getTestCasesDirectory(), "test cases must be available");

    /**
     * Reset all counters associated with this service.
     * Only use this method if the proof is empty!
     */
    public void resetCounters(Proof proof) {
        final Node root = Objects.requireNonNull(proof.root(), "the proof has a root node");
        if (root.childrenCount() > 0) {
            throw new IllegalStateException("tried to reset counters on non-empty proof");
        }

        try {
            final HashMap<String, Counter> counters =
                HelperClassForTests.get(proof.getServices(), "counters");
            counters.clear();
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
            final Node root1 = Objects.requireNonNull(proof1.root(), "the proof has a root node");
            final Node root2 = Objects.requireNonNull(proof2.root(), "the proof has a root node");
            proof2.pruneProof(root2);
            resetCounters(proof2);
            final Goal openGoal =
                Objects.requireNonNull(proof2.getOpenGoal(root2), "the root holds an open goal");
            new CopyingProofReplayer(proof1, proof2).copy(root1, openGoal, new HashSet<>());

            assertTrue(proof2.closed());
            Assertions.assertEquals(proof1.countNodes(), proof2.countNodes());

            GeneralSettings.noPruningClosed = true;
        }
    }
}
