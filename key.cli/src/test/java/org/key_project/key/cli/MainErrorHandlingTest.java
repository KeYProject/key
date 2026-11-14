/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli;

import java.io.PrintWriter;
import java.io.StringWriter;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for the mapping of execution-time exceptions to {@code KEY_ERROR} lines and exit codes
 * (§1): {@link CliError}s are reported with their kind's exit code, anything else is an internal
 * error with exit code 4.
 */
class MainErrorHandlingTest {

    private final StringWriter err = new StringWriter();

    @Test
    void inputCliErrorPrintsKeyErrorAndExits3() {
        int code = Main.handleExecutionException(CliError.input("bad input"), new PrintWriter(err));

        assertThat(code).isEqualTo(ExitCode.INPUT_ERROR.code());
        assertThat(err.toString()).contains("KEY_ERROR bad input");
    }

    @Test
    void internalCliErrorPrintsKeyErrorAndExits4() {
        int code = Main.handleExecutionException(
            CliError.internal("processing crashed"), new PrintWriter(err));

        assertThat(code).isEqualTo(ExitCode.INTERNAL_ERROR.code());
        assertThat(err.toString()).contains("KEY_ERROR processing crashed");
    }

    @Test
    void unexpectedExceptionIsAnInternalError() {
        int code =
            Main.handleExecutionException(new RuntimeException("boom"), new PrintWriter(err));

        assertThat(code).isEqualTo(ExitCode.INTERNAL_ERROR.code());
        assertThat(err.toString()).contains("KEY_ERROR internal error: boom");
    }

    @Test
    void unexpectedExceptionWithoutMessageUsesTheExceptionName() {
        int code =
            Main.handleExecutionException(new NullPointerException(), new PrintWriter(err));

        assertThat(code).isEqualTo(ExitCode.INTERNAL_ERROR.code());
        assertThat(err.toString()).contains("KEY_ERROR internal error: NullPointerException");
    }
}
