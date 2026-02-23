/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testfixtures;

import java.util.Optional;

import org.junit.jupiter.api.extension.AfterAllCallback;
import org.junit.jupiter.api.extension.BeforeAllCallback;
import org.junit.jupiter.api.extension.ExtensionContext;
import org.junit.jupiter.api.extension.TestWatcher;

/// A JUnit extension to print out workflow commands of Github actions to make logs more accessible.
///
/// [See Github's
/// documentation.](https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-commands#grouping-log-lines)
///
/// @author Alexander Weigl
/// @version 1 (2026-02-23)
public class GithubTestPrinter implements TestWatcher, BeforeAllCallback, AfterAllCallback {
    private static final boolean ENABLED = "true".equals(System.getenv("CI"));

    @Override
    public void testAborted(ExtensionContext context, Throwable cause) {
        if (ENABLED) {
            return;
        }
        System.out.format("::error title=Test aborted %s::Test %s#%s aborted due to \"%s: %s\"%n",
            context.getDisplayName(),
            context.getRequiredTestClass().getName(),
            context.getRequiredTestMethod().getName(),
            cause.getClass().getName(), cause.getMessage());
    }

    @Override
    public void testDisabled(ExtensionContext context, Optional<String> reason) {
        if (ENABLED) {
            return;
        }
        System.out.format("::notice title=Disabled test %s::Test %s#%s disabled due to %s%n",
            context.getDisplayName(),
            context.getRequiredTestClass().getName(),
            context.getRequiredTestMethod().getName(),
            reason.orElse("no reason given"));
    }

    @Override
    public void testFailed(ExtensionContext context, Throwable cause) {
        if (ENABLED) {
            return;
        }
        System.out.format("::error title=Test failed %s::Test %s#%s aborted due to \"%s: %s\"%n",
            context.getDisplayName(),
            context.getRequiredTestClass().getName(),
            context.getRequiredTestMethod().getName(),
            cause.getClass().getName(), cause.getMessage());
    }

    @Override
    public void testSuccessful(ExtensionContext context) {
        if (ENABLED) {
            return;
        }
        System.out.format("::debug::SUCCESS:%s%n", context.getDisplayName());
    }


    @Override
    public void beforeAll(ExtensionContext context) {
        if (ENABLED) {
            return;
        }
        System.out.format("::group::%s%n", context.getDisplayName());
    }

    @Override
    public void afterAll(ExtensionContext context) {
        if (ENABLED) {
            return;
        }
        System.out.format("::endgroup::");
    }
}
