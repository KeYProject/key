/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.njml;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Test;

/**
 * Tests the translation of JML assertion statements ({@code //@ assert}) in all positions of a
 * method body.
 */
class JmlAssertLoadingTest {
    /**
     * An assertion in the then-branch of an {@code if} with an {@code else} must be translated
     * when the enclosing method body is loaded. All local variables visible at the assertion have
     * to be collected, walking both branches of the {@code if}.
     *
     * @throws Exception if loading fails
     */
    @Test
    void assertInsideThenBranchWithElse() throws Exception {
        Path javaFile =
            HelperClassForTests.TESTCASE_DIRECTORY.resolve("jmlAssert/IfAssert.java");
        Assumptions.assumeTrue(Files.exists(javaFile));
        KeYEnvironment<?> env = KeYEnvironment.load(javaFile);
        Assertions.assertNotNull(env.getServices());
    }
}
