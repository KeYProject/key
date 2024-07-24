/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.util;

import java.io.File;

import org.key_project.rusty.proof.ProofAggregate;
import org.key_project.rusty.proof.init.*;
import org.key_project.rusty.proof.io.RuleSourceFactory;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.helper.FindResources;

import static org.key_project.rusty.proof.io.RuleSource.LDT_FILE;

public class TestHelper {
    public static final File TESTCASE_DIRECTORY = FindResources.getTestCasesDirectory();
    public static final File DUMMY_KEY_FILE = new File(TESTCASE_DIRECTORY, "dummyTrue.key");

    public static final Profile profile = new RustProfile() {
        @Override
        public RuleCollection getStandardRules() {
            return new RuleCollection(RuleSourceFactory.fromDefaultLocation(LDT_FILE), ImmutableSLList.nil());
        }
    };

    public TestHelper() {

    }

    public ProofAggregate parse(File file, Profile profile) {
        ProblemInitializer pi = null;
        ProofAggregate result = null;

        try {
            KeYUserProblemFile po = new KeYUserProblemFile("UpdatetermTest", file, profile);
            pi = new ProblemInitializer(profile);

            // result = pi.startProver(po, po);

        } catch (Exception e) {
            throw new RuntimeException(e);
        }
        //return result;
        return null;
    }
}
