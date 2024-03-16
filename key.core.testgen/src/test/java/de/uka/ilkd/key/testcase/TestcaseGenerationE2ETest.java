/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testcase;

import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.testgen.TGMain;

import org.junit.jupiter.api.Test;

/**
 * @author Alexander Weigl
 * @version 1 (03.02.24)
 */
public class TestcaseGenerationE2ETest {
    @Test
    public void binarySearch() throws ProblemLoaderException, InterruptedException {
        TGMain.main(new String[] {
            "--output", "testcases/binarysearch/actual", "testcases/binarysearch/attempt.proof"
        });
    }

    @Test
    public void arrayUtil() throws ProblemLoaderException, InterruptedException {
        TGMain.main(new String[] {
            "--all-contracts",
            "--output", "testcases/arrayutil/actual",
            "testcases/arrayutil/src/"
        });
    }
}
