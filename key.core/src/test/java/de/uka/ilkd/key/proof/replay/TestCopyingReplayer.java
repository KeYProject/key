/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.replay;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashSet;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.GeneralSettings;

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
            proof2.getServices().resetCounters();
            new CopyingProofReplayer(proof1, proof2).copy(proof1.root(),
                    proof2.getOpenGoal(proof2.root()), new HashSet<>());

            assertTrue(proof2.closed());
            Assertions.assertEquals(proof1.countNodes(), proof2.countNodes());

            GeneralSettings.noPruningClosed = true;
        }
    }
}
