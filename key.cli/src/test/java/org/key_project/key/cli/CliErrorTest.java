/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli;

import java.nio.file.Path;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for the central {@link CliError} type and its error-kind → exit-code mapping (§1 of the
 * headless interface spec).
 */
class CliErrorTest {

    @Test
    void inputErrorMapsToExitCode3() {
        CliError error = CliError.input("bad input");

        assertThat(error.kind()).isEqualTo(CliError.Kind.INPUT);
        assertThat(error.kind().exitCode()).isEqualTo(ExitCode.INPUT_ERROR);
        assertThat(requireMessage(error)).isEqualTo("bad input");
        assertThat(error.getCause() == null).isTrue();
    }

    @Test
    void internalErrorMapsToExitCode4() {
        RuntimeException cause = new RuntimeException("boom");
        CliError error = CliError.internal("something broke", cause);

        assertThat(error.kind()).isEqualTo(CliError.Kind.INTERNAL);
        assertThat(error.kind().exitCode()).isEqualTo(ExitCode.INTERNAL_ERROR);
        assertThat(requireMessage(error)).isEqualTo("something broke");
        assertThat(requireCause(error)).isSameAs(cause);
    }

    @Test
    void loadFailureWithoutInternalCauseIsAnInputError() {
        RuntimeException cause =
            new IllegalStateException("syntax error near line 1", new IllegalArgumentException());
        CliError error = CliError.loadFailure(Path.of("bad.key"), cause);

        assertThat(error.kind()).isEqualTo(CliError.Kind.INPUT);
        assertThat(error.kind().exitCode()).isEqualTo(ExitCode.INPUT_ERROR);
        assertThat(requireMessage(error)).contains("bad.key");
        assertThat(requireMessage(error)).contains("syntax error near line 1");
        assertThat(requireCause(error)).isSameAs(cause);
    }

    @Test
    void loadFailureWithNullPointerExceptionCauseIsInternal() {
        CliError error = CliError.loadFailure(Path.of("bad.key"),
            new IllegalStateException("loading failed", new NullPointerException()));

        assertThat(error.kind()).isEqualTo(CliError.Kind.INTERNAL);
        assertThat(error.kind().exitCode()).isEqualTo(ExitCode.INTERNAL_ERROR);
    }

    @Test
    void loadFailureWithNestedNpeCauseIsInternal() {
        RuntimeException cause = new IllegalStateException("wrapper",
            new IllegalArgumentException("deeper", new NullPointerException()));
        CliError error = CliError.loadFailure(Path.of("bad.key"), cause);

        assertThat(error.kind()).isEqualTo(CliError.Kind.INTERNAL);
    }

    @Test
    void oneLineCollapsesWhitespaceAndLineBreaks() {
        assertThat(CliError.oneLine("  failed:\n  line 2\tat  ")).isEqualTo("failed: line 2 at");
    }

    @Test
    void loadFailurePrefersTheInformativeCauseOverTheLoaderSummary() {
        RuntimeException cause =
            new IllegalStateException("Failed to parse Bad.java:2/27: syntax error");
        CliError error =
            CliError.loadFailure(Path.of("Bad.java"), new RuntimeException("Load failed", cause));

        assertThat(requireMessage(error))
                .isEqualTo("cannot load 'Bad.java': Failed to parse Bad.java:2/27: syntax error");
    }

    @Test
    void loadFailureFlattensAMultiLineCauseToOneLine() {
        RuntimeException cause =
            new IllegalStateException("Error occurred:\nBad.java:2/27: (line 2,col 27) boom");
        CliError error =
            CliError.loadFailure(Path.of("Bad.java"), new RuntimeException("Load failed", cause));

        assertThat(requireMessage(error))
                .isEqualTo(
                    "cannot load 'Bad.java': Error occurred: Bad.java:2/27: (line 2,col 27) boom");
    }

    @Test
    void loadFailureWithoutAnyCauseMessageKeepsTheLoaderSummary() {
        CliError error = CliError.loadFailure(Path.of("bad.key"),
            new RuntimeException("Load failed", new IllegalArgumentException()));

        assertThat(requireMessage(error)).isEqualTo("cannot load 'bad.key': Load failed");
    }

    @Test
    void isInternalCauseIgnoresUnrelatedCycles() {
        IllegalStateException cause = new IllegalStateException("loop");
        IllegalStateException cause2 = new IllegalStateException("loop2", cause);
        cause.initCause(cause2);

        assertThat(CliError.isInternalCause(cause)).isFalse();
        assertThat(CliError.isInternalCause(new NullPointerException())).isTrue();
    }

    private static String requireMessage(CliError error) {
        String message = error.getMessage();
        if (message == null) {
            throw new AssertionError("expected a non-null error message");
        }
        return message;
    }

    private static Throwable requireCause(CliError error) {
        Throwable cause = error.getCause();
        if (cause == null) {
            throw new AssertionError("expected a non-null cause");
        }
        return cause;
    }
}
