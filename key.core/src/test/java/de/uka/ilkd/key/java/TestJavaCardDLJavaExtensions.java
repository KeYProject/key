/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import java.io.File;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class TestJavaCardDLJavaExtensions {

    private final HelperClassForTests helper = new HelperClassForTests();

    public static final String testpath = HelperClassForTests.TESTCASE_DIRECTORY + File.separator
        + "javacardDLExtensions" + File.separator;


    public TestJavaCardDLJavaExtensions() {

    }

    @Test
    public void testTypeNotInScopeShouldNotBeFound() {
        try {
            helper.parseThrowException(new File(testpath + "typeResolutionInMethodFrame.key"));
        } catch (Throwable t) {
            return;
        }
        Assertions.fail("Something with type resolution in method frames is corrupt. "
            + "The type Test should not be found in the default scope as it is "
            + "declared inside package test.");
    }

    @Test
    public void testMethodFrameRedirectsScope() throws ProofInputException {
        helper.parseThrowException(new File(testpath + "typeResolutionInMethodFrame2.key"));
        /*
         * fail("Something with type resolution in method frames is corrupt. " +
         * "The type Test should be found as the scope to look for " +
         * "is redirected to test.Test");
         */ }
}
