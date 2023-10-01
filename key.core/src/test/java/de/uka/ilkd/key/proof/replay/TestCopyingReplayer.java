/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.replay;

import java.io.File;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.GeneralSettings;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

/**
 * Tests for {@link CopyingProofReplayer}.
 *
 * @author Arne Keller
 */
class TestCopyingReplayer {
    public static final File testCaseDirectory = FindResources.getTestCasesDirectory();

    @Test
    void testJavaProof() throws Exception {
        GeneralSettings.noPruningClosed = false;

        KeYEnvironment<DefaultUserInterfaceControl> env =
            KeYEnvironment.load(new File(testCaseDirectory,
                "../../../../../key.ui/examples/heap/verifyThis15_1_RelaxedPrefix/relax.proof"));
        Assertions.assertNotNull(env.getLoadedProof());
        Assertions.assertTrue(env.getLoadedProof().closed());
        KeYEnvironment<DefaultUserInterfaceControl> env2 =
            KeYEnvironment.load(new File(testCaseDirectory,
                "../../../../../key.ui/examples/heap/verifyThis15_1_RelaxedPrefix/relax.proof"));
        Assertions.assertNotNull(env2.getLoadedProof());
        Assertions.assertTrue(env2.getLoadedProof().closed());

        Proof proof1 = env.getLoadedProof();
        Proof proof2 = env2.getLoadedProof();

        // clear proof2, replay proof1 on top
        proof2.pruneProof(proof2.root());
        proof2.getServices().resetCounters();
        new CopyingProofReplayer(proof1, proof2).copy(proof1.root(),
            proof2.getOpenGoal(proof2.root()));

        Assertions.assertTrue(proof2.closed());
        Assertions.assertEquals(proof1.countNodes(), proof2.countNodes());

        GeneralSettings.noPruningClosed = true;
    }
}
