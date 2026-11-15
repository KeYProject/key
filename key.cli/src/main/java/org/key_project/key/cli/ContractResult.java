/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli;

import java.nio.file.Path;

import org.jspecify.annotations.Nullable;

/**
 * The outcome of proving a single contract. One instance is rendered as one {@code KEY_RESULT}
 * line by {@link ResultRecordWriter}.
 *
 * @param contract the canonical contract name that was proven
 * @param status the final outcome of this contract
 * @param openGoals number of goals still open at termination: {@code 0} when the status is
 *        {@link ResultStatus#CLOSED} or {@link ResultStatus#ERROR}, and at least {@code 1} when
 *        it is {@link ResultStatus#OPEN} or {@link ResultStatus#TIMED_OUT}
 * @param elapsedMs wall-clock milliseconds spent in proof search for this contract
 * @param proofFile absolute path of the written proof file, or {@code null}
 * @param smtCalls number of SMT solver invocations ({@code 0} unless SMT is enabled)
 * @param smtProved number of goals proved via SMT ({@code 0} unless SMT is enabled)
 * @param errorMessage human-readable error message, non-{@code null} iff the status is
 *        {@link ResultStatus#ERROR}
 */
public record ContractResult(String contract, ResultStatus status, int openGoals, long elapsedMs,
        @Nullable Path proofFile, int smtCalls, int smtProved, @Nullable String errorMessage) {
}
