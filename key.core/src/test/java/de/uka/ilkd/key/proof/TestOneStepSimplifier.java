/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.io.File;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class TestOneStepSimplifier {
    public static final File testCaseDirectory = FindResources.getTestCasesDirectory();

    @Test
    void loadWithRestriction() throws ProblemLoaderException {
        // test to verify that the One Step Simplifier only uses formulas specified in the proof
        // file to instantiate assumptions
        // (if more rules are added to the OSS set, this restriction may increase the chances that
        // old proofs still load)
        KeYEnvironment<DefaultUserInterfaceControl> env =
            KeYEnvironment.load(new File(testCaseDirectory, "ossRestriction.proof"));
        Assertions.assertNotNull(env.getLoadedProof());
        Assertions.assertTrue(env.getLoadedProof().closed());
    }
}
