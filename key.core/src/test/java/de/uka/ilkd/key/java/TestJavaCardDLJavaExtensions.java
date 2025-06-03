/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import java.nio.file.Path;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.util.HelperClassForTests;
import de.uka.ilkd.key.util.parsing.BuildingException;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class TestJavaCardDLJavaExtensions {

    public static final Path testpath =
        HelperClassForTests.TESTCASE_DIRECTORY.resolve("javacardDLExtensions");


    public TestJavaCardDLJavaExtensions() {

    }

    @Test
    public void testTypeNotInScopeShouldNotBeFound() {
        var message = "Something with type resolution in method frames is corrupt. "
            + "The type Test should not be found in the default scope as it is "
            + "declared inside package test.";
        Assertions.assertThrows(BuildingException.class,
            () -> HelperClassForTests
                    .parseThrowException(testpath.resolve("typeResolutionInMethodFrame.key")),
            message);
    }

    @Test
    public void testMethodFrameRedirectsScope() throws ProofInputException {
        HelperClassForTests
                .parseThrowException(testpath.resolve("typeResolutionInMethodFrame2.key"));
    }
}
