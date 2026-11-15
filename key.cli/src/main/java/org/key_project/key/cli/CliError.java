/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli;

import java.nio.file.Path;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Set;

import de.uka.ilkd.key.proof.io.ConstructNotSupportedException;

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
     * treated as internal bugs (exit 4). A
     * {@link ConstructNotSupportedException} in the cause chain (an unsupported JML/Java
     * construct, §8 of the headless interface spec) is always an input error whose message is the
     * structured construct diagnostic, passed through verbatim.
     *
     * @param file the problem file that could not be loaded
     * @param cause the loader exception
     * @return the classified error
     */
    public static CliError loadFailure(Path file, Throwable cause) {
        ConstructNotSupportedException constructError =
            findCause(cause, ConstructNotSupportedException.class);
        if (constructError != null) {
            return input(constructError.formattedMessage(), constructError);
        }
        String message = "cannot load '" + file + "': " + loadFailureReason(cause);
        return isInternalCause(cause) ? internal(message, cause) : input(message, cause);
    }

    /**
     * Creates the error record reported for a file that could not be loaded: the record's
     * {@code contract} field names the failed input file, and its {@code errorMessage} carries
     * the loader's failure message (see {@link #loadFailureMessage(Path, Throwable)}). Both the
     * {@code prove} and the {@code script} subcommand print this record before the
     * {@code KEY_ERROR} line of {@link #loadFailure(Path, Throwable)}.
     *
     * @param file the file that could not be loaded
     * @param cause the loader exception
     * @return the error record for the failed file
     */
    public static ContractResult loadFailureRecord(Path file, Throwable cause) {
        return new ContractResult(file.toString(), ResultStatus.ERROR, 0, 0, null, 0, 0,
            loadFailureMessage(file, cause));
    }

    /**
     * Returns the message reported for a failure to load a problem file: the structured
     * construct diagnostic (see {@link #loadFailure(Path, Throwable)}) when the cause chain
     * carries a {@link ConstructNotSupportedException}, and the most informative available
     * reason otherwise (see {@link #loadFailureReason(Throwable)}).
     *
     * @param file the problem file that could not be loaded
     * @param cause the loader exception
     * @return the message for the error record's {@code errorMessage} field
     */
    public static String loadFailureMessage(Path file, Throwable cause) {
        ConstructNotSupportedException constructError =
            findCause(cause, ConstructNotSupportedException.class);
        if (constructError != null) {
            return constructError.formattedMessage();
        }
        return "cannot load '" + file + "': " + loadFailureReason(cause);
    }

    /**
     * Selects the most informative single-line reason from a loader exception's cause chain.
     * <p>
     * The loader's own message is a constant summary (currently {@code "Load failed"}), while the
     * actionable diagnostic — often with file, line and column — is carried by a deeper cause.
     * This method therefore prefers the first non-blank message that differs from the top-level
     * one, falls back to the top-level message, and finally to the exception's simple class name.
     * Newlines are collapsed because the result is emitted on a line-oriented protocol.
     *
     * @param cause the loader exception
     * @return the flattened reason
     */
    private static String loadFailureReason(Throwable cause) {
        String summary = cause.getMessage();
        Set<Throwable> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        for (Throwable c = cause; c != null && seen.add(c); c = c.getCause()) {
            String message = c.getMessage();
            if (message != null && !message.isBlank() && !message.equals(summary)) {
                return oneLine(message);
            }
        }
        return summary != null && !summary.isBlank() ? oneLine(summary)
                : cause.getClass().getSimpleName();
    }

    /**
     * Collapses a possibly multi-line message into a single line with collapsed whitespace, as
     * required by the line-oriented protocol (§2 of the headless interface spec).
     *
     * @param message the message to flatten
     * @return the message without line breaks or leading/trailing whitespace
     */
    public static String oneLine(String message) {
        return message.strip().replaceAll("\\s+", " ");
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

    /**
     * Returns the first throwable of the given type in the cause chain (including the throwable
     * itself), or {@code null} if absent. Cycle-safe.
     *
     * @param throwable the exception to inspect
     * @param type the type to look for
     * @param <T> the throwable type
     * @return the first matching throwable, or {@code null}
     */
    static @Nullable <T extends Throwable> T findCause(Throwable throwable, Class<T> type) {
        Set<Throwable> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        for (Throwable c = throwable; c != null && seen.add(c); c = c.getCause()) {
            if (type.isInstance(c)) {
                return type.cast(c);
            }
        }
        return null;
    }
}
