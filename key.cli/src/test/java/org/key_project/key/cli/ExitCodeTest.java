/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli;

import java.util.ArrayList;
import java.util.List;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for {@link ExitCode}, in particular {@link ExitCode#worstOf}.
 */
class ExitCodeTest {

    private static ContractResult result(ResultStatus status) {
        return new ContractResult("c".concat(status.name()), status, 0, 0, null, 0, 0, null);
    }

    @Test
    void codeValues() {
        assertThat(ExitCode.CLOSED.code()).isEqualTo(0);
        assertThat(ExitCode.OPEN.code()).isEqualTo(1);
        assertThat(ExitCode.TIMED_OUT.code()).isEqualTo(2);
        assertThat(ExitCode.INPUT_ERROR.code()).isEqualTo(3);
        assertThat(ExitCode.INTERNAL_ERROR.code()).isEqualTo(4);
    }

    @Test
    void worstOfEmptyIsClosed() {
        assertThat(ExitCode.worstOf(List.of())).isEqualTo(ExitCode.CLOSED);
    }

    @Test
    void worstOfSingleResult() {
        assertThat(ExitCode.worstOf(List.of(result(ResultStatus.CLOSED))))
                .isEqualTo(ExitCode.CLOSED);
        assertThat(ExitCode.worstOf(List.of(result(ResultStatus.OPEN)))).isEqualTo(ExitCode.OPEN);
        assertThat(ExitCode.worstOf(List.of(result(ResultStatus.TIMED_OUT))))
                .isEqualTo(ExitCode.TIMED_OUT);
        assertThat(ExitCode.worstOf(List.of(result(ResultStatus.ERROR))))
                .isEqualTo(ExitCode.INTERNAL_ERROR);
    }

    @Test
    void worstOfAllPairs() {
        // declaration order of ResultStatus equals the severity order CLOSED < OPEN < TIMED_OUT <
        // ERROR, so the worst of a pair is the one with the greater ordinal
        ResultStatus[] statuses = ResultStatus.values();
        for (int i = 0; i < statuses.length; i++) {
            for (int j = 0; j < statuses.length; j++) {
                List<ContractResult> results =
                    List.of(result(statuses[i]), result(statuses[j]));
                ResultStatus worst = statuses[Math.max(i, j)];
                ExitCode expected = ExitCode.fromStatus(worst);
                assertThat(ExitCode.worstOf(results))
                        .as("worstOf(%s, %s)", statuses[i], statuses[j]).isEqualTo(expected);
            }
        }
    }

    @Test
    void worstOfMixedSet() {
        List<ContractResult> results = new ArrayList<>();
        results.add(result(ResultStatus.CLOSED));
        results.add(result(ResultStatus.ERROR));
        results.add(result(ResultStatus.OPEN));
        assertThat(ExitCode.worstOf(results)).isEqualTo(ExitCode.INTERNAL_ERROR);

        results = new ArrayList<>();
        results.add(result(ResultStatus.TIMED_OUT));
        results.add(result(ResultStatus.CLOSED));
        results.add(result(ResultStatus.OPEN));
        assertThat(ExitCode.worstOf(results)).isEqualTo(ExitCode.TIMED_OUT);
    }
}
