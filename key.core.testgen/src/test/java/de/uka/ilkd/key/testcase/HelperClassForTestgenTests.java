/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.testcase;

import java.nio.file.Path;

import org.key_project.util.helper.FindResources;

import static org.junit.jupiter.api.Assertions.assertNotNull;

public class HelperClassForTestgenTests {
    public static final Path TESTCASE_DIRECTORY = FindResources.getTestCasesDirectory();

    static {
        assertNotNull(TESTCASE_DIRECTORY, "Could not find test case directory");
    }
}
