/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.util;

import java.io.File;

import org.key_project.rusty.proof.ProofAggregate;
import org.key_project.rusty.proof.init.KeYUserProblemFile;
import org.key_project.rusty.proof.init.ProblemInitializer;
import org.key_project.rusty.proof.init.Profile;
import org.key_project.util.helper.FindResources;

public class TestHelper {
    public static final File TESTCASE_DIRECTORY = FindResources.getTestCasesDirectory();
    public static final File DUMMY_KEY_FILE = new File(TESTCASE_DIRECTORY, "dummyTrue.key");

    public TestHelper() {

    }

    public ProofAggregate parse(File file, Profile profile) {
        ProblemInitializer pi = null;
        ProofAggregate result = null;

        try {
            KeYUserProblemFile po = new KeYUserProblemFile("UpdatetermTest", file, profile);
            pi = new ProblemInitializer(profile);

            result = pi.startProver(po, po);

        } catch (Exception e) {
            throw new RuntimeException(e);
        }
        return result;
    }
}
