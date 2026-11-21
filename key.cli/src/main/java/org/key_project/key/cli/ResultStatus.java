/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli;

/**
 * Status of a single contract after proof search, as printed in the {@code status} field of a
 * {@code KEY_RESULT} record.
 * <p>
 * The values are ordered from best to worst ({@code CLOSED < OPEN < TIMED_OUT < ERROR}); see
 * {@link #worseThan(ResultStatus)}.
 */
public enum ResultStatus {
    /// The proof of the contract was closed.
    CLOSED("closed", 0),
    /// The proof search terminated with at least one open goal.
    OPEN("open", 1),
    /// The proof search was abandoned because of the timeout without a decision.
    TIMED_OUT("timed_out", 2),
    /// The contract could not be proven because of an error.
    ERROR("error", 3);

    private final String statusString;
    private final int severity;

    ResultStatus(String statusString, int severity) {
        this.statusString = statusString;
        this.severity = severity;
    }

    /**
     * Returns the literal value of the {@code status} field of a {@code KEY_RESULT} record.
     *
     * @return one of {@code "closed"}, {@code "open"}, {@code "timed_out"}, {@code "error"}
     */
    public String statusString() {
        return statusString;
    }

    /**
     * Tells whether this status is strictly worse than the given status in the sense of the
     * headless interface contract: {@code ERROR > TIMED_OUT > OPEN > CLOSED}.
     *
     * @param other the status to compare against
     * @return {@code true} iff this status is strictly worse than {@code other}
     */
    public boolean worseThan(ResultStatus other) {
        return severity > other.severity;
    }
}
