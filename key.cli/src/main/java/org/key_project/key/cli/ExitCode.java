/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli;

/**
 * Process exit codes of the headless CLI, as specified by §1 of the interface contract.
 */
public enum ExitCode {
    /// All selected contracts were closed.
    CLOSED(0),
    /// At least one selected contract has an open goal.
    OPEN(1),
    /// The proof search was abandoned because of a timeout.
    TIMED_OUT(2),
    /// The input was invalid (missing file, parse error, unknown option, ...).
    INPUT_ERROR(3),
    /// An error not attributable to the input occurred.
    INTERNAL_ERROR(4);

    private final int code;

    ExitCode(int code) {
        this.code = code;
    }

    /**
     * Returns the numeric process exit code.
     *
     * @return the exit code, between {@code 0} and {@code 4}
     */
    public int code() {
        return code;
    }

    /**
     * Maps a contract status to the corresponding exit code. A contract with status
     * {@link ResultStatus#ERROR} maps to {@link #INTERNAL_ERROR}, since a per-contract failure is
     * not attributable to the command-line input.
     *
     * @param status the status to map
     * @return the exit code for the status
     */
    public static ExitCode fromStatus(ResultStatus status) {
        return switch (status) {
            case CLOSED -> CLOSED;
            case OPEN -> OPEN;
            case TIMED_OUT -> TIMED_OUT;
            case ERROR -> INTERNAL_ERROR;
        };
    }

    /**
     * Returns the worst exit code among the given results, i.e. the one reflecting the worst
     * status. An empty iterable yields {@link #CLOSED}.
     *
     * @param results the contract results to inspect
     * @return the worst exit code
     */
    public static ExitCode worstOf(Iterable<ContractResult> results) {
        ExitCode worst = CLOSED;
        for (ContractResult result : results) {
            ExitCode candidate = fromStatus(result.status());
            if (candidate.code > worst.code) {
                worst = candidate;
            }
        }
        return worst;
    }
}
