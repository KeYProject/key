/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import java.nio.file.Path;

import de.uka.ilkd.key.util.HelperClassForTests;

import com.github.javaparser.resolution.UnsolvedSymbolException;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class TestJavaDLASTExtensions {

    public static final Path testpath =
        HelperClassForTests.TESTCASE_DIRECTORY.resolve("javaASTExtensions");


    public TestJavaDLASTExtensions() {
    }

    @Test
    public void testTypeNotInScopeShouldNotBeFound() {
        var message = "Something with type resolution in method frames is corrupt. "
            + "The type TestJavaCardDLExtensions should not be found in the default scope as it is "
            + "declared inside package sub1.";
        Assertions.assertThrows(UnsolvedSymbolException.class,
            () -> HelperClassForTests
                    .parseThrowException(
                        testpath.resolve("typeResolutionInMethodFrameNotResolvable.key")),
            message);
    }

    @Test
    public void testMethodFrameRedirectsScope() {
        try {
            HelperClassForTests
                    .parseThrowException(
                        testpath.resolve("typeResolutionInMethodFrameResolvable.key"));
        } catch (Throwable t) {
            Assertions.fail(
                "Resolution of type TestJavaCardDLExtensions should be successful as the enclosing method frame redirects the scope to package sub1\n"
                    + t);
        }
    }

    // similar tests to the ones above but with nested method frames to ensure that the redirects of
    // both are respected
    @Test
    public void testTypeNotInInnerScopeShouldNotBeFound() {
        var message = "Something with type resolution in method frames is corrupt. "
            + "The type TestJavaCardDLExtensions should not be found as it is "
            + "declared inside package sub1, but resolved in package sub2 (redirect by method-frame)";
        Assertions.assertThrows(UnsolvedSymbolException.class,
            () -> HelperClassForTests
                    .parseThrowException(
                        testpath.resolve("typeResolutionInNestedMethodFrameNotResolvable.key")),
            message);
    }

    @Test
    public void testNestedMethodFrameRedirects() {
        try {
            HelperClassForTests
                    .parseThrowException(
                        testpath.resolve("typeResolutionInNestedMethodFrameResolvable.key"));
        } catch (Throwable t) {
            Assertions.fail("Resolution of type " +
                "TestJavaCardDLExtensions should be successful as it is enclosed by the outer method frame "
                +
                "which redirects the scope to package sub1. Class Third should be resolvable (and visible) as the"
                +
                "inner method-frame redirects to package sub2.\n " + t);
        }

    }



}
