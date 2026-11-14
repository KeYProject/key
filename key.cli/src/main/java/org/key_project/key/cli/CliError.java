/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli;

import java.nio.file.Path;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Set;

import org.jspecify.annotations.Nullable;

/**
 * The central error type of the headless CLI (§1 of the headless interface spec).
 * <p>
 * Every CLI-level error is reported as a single {@code KEY_ERROR} line on stderr, and the process
 * exits with the exit code of the error's kind: {@link Kind#INPUT} ({@code 3}) for problems that
 * are attributable to the input (missing file, parse error, unknown option, unknown contract, bad
 * settings) and {@link Kind#INTERNAL} ({@code 4}) for errors that are not. Commands throw
 * {@code CliError} instead of printing and returning an exit code themselves; the root command
 * line's execution-exception handler performs the mapping.
 */
public final class CliError extends RuntimeException {

    /**
     * The kind of a CLI error, mapped to the corresponding process exit code.
     */
    public enum Kind {
        /// The input was invalid (file not found, parse error, unknown option, ...).
        INPUT(ExitCode.INPUT_ERROR),
        /// An error not attributable to the input occurred.
        INTERNAL(ExitCode.INTERNAL_ERROR);

        private final ExitCode exitCode;

        Kind(ExitCode exitCode) {
            this.exitCode = exitCode;
        }

        /**
         * Returns the process exit code for this kind.
         *
         * @return {@code 3} for {@link #INPUT}, {@code 4} for {@link #INTERNAL}
         */
        public ExitCode exitCode() {
            return exitCode;
        }
    }

    private final Kind kind;

    private CliError(Kind kind, String message, @Nullable Throwable cause) {
        super(message, cause);
        this.kind = kind;
    }

    /**
     * Returns the kind of this error.
     *
     * @return {@link Kind#INPUT} or {@link Kind#INTERNAL}
     */
    public Kind kind() {
        return kind;
    }

    /**
     * Creates an input error (exit code 3).
     *
     * @param message the human-readable error message (printed after {@code KEY_ERROR })
     * @return the input error
     */
    public static CliError input(String message) {
        return new CliError(Kind.INPUT, message, null);
    }

    /**
     * Creates an input error (exit code 3) with a cause.
     *
     * @param message the human-readable error message (printed after {@code KEY_ERROR })
     * @param cause the underlying failure, if any
     * @return the input error
     */
    public static CliError input(String message, @Nullable Throwable cause) {
        return new CliError(Kind.INPUT, message, cause);
    }

    /**
     * Creates an internal error (exit code 4).
     *
     * @param message the human-readable error message (printed after {@code KEY_ERROR })
     * @return the internal error
     */
    public static CliError internal(String message) {
        return new CliError(Kind.INTERNAL, message, null);
    }

    /**
     * Creates an internal error (exit code 4) with a cause.
     *
     * @param message the human-readable error message (printed after {@code KEY_ERROR })
     * @param cause the underlying failure, if any
     * @return the internal error
     */
    public static CliError internal(String message, @Nullable Throwable cause) {
        return new CliError(Kind.INTERNAL, message, cause);
    }

    /**
     * Classifies a failure to load a problem file. Load failures are input errors (exit 3) unless
     * the cause chain contains a {@link NullPointerException} or an {@link Error}, which are
     * treated as internal bugs (exit 4).
     *
     * @param file the problem file that could not be loaded
     * @param cause the loader exception
     * @return the classified error
     */
    public static CliError loadFailure(Path file, Throwable cause) {
        String message = "cannot load '" + file + "': "
            + (cause.getMessage() != null ? cause.getMessage()
                    : cause.getClass().getSimpleName());
        return isInternalCause(cause) ? internal(message, cause) : input(message, cause);
    }

    /**
     * Tells whether the given exception (or any of its causes) is a {@link NullPointerException}
     * or an {@link Error}, i.e. an internal bug rather than invalid input.
     *
     * @param throwable the exception to inspect
     * @return {@code true} iff the cause chain contains an NPE or an {@code Error}
     */
    static boolean isInternalCause(Throwable throwable) {
        Set<Throwable> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        for (Throwable c = throwable; c != null && seen.add(c); c = c.getCause()) {
            if (c instanceof NullPointerException || c instanceof Error) {
                return true;
            }
        }
        return false;
    }
}
