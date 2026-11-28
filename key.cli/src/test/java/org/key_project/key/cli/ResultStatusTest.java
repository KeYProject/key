/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli;

import java.util.List;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for {@link ResultStatus}, in particular the worst-order relation required by the headless
 * interface contract (§1): {@code ERROR > TIMED_OUT > OPEN > CLOSED}.
 */
class ResultStatusTest {

    /// The intended worst-order, from best to worst.
    private static final List<ResultStatus> ORDER =
        List.of(ResultStatus.CLOSED, ResultStatus.OPEN, ResultStatus.TIMED_OUT,
            ResultStatus.ERROR);

    @Test
    void statusStrings() {
        assertThat(ResultStatus.CLOSED.statusString()).isEqualTo("closed");
        assertThat(ResultStatus.OPEN.statusString()).isEqualTo("open");
        assertThat(ResultStatus.TIMED_OUT.statusString()).isEqualTo("timed_out");
        assertThat(ResultStatus.ERROR.statusString()).isEqualTo("error");
    }

    @Test
    void allStatusesHaveDistinctStatusStrings() {
        assertThat(ResultStatus.values()).extracting(ResultStatus::statusString)
                .doesNotHaveDuplicates();
    }

    @Test
    void pairwiseWorstOrder() {
        for (int i = 0; i < ORDER.size(); i++) {
            for (int j = 0; j < ORDER.size(); j++) {
                ResultStatus a = ORDER.get(i);
                ResultStatus b = ORDER.get(j);
                assertThat(a.worseThan(b)).as("%s worseThan %s", a, b)
                        .isEqualTo(i > j);
                assertThat(b.worseThan(a)).as("%s worseThan %s", b, a)
                        .isEqualTo(j > i);
            }
        }
    }

    @Test
    void nothingIsWorseThanError() {
        for (ResultStatus s : ResultStatus.values()) {
            assertThat(s.worseThan(ResultStatus.ERROR)).isFalse();
        }
        assertThat(ResultStatus.ERROR.worseThan(ResultStatus.CLOSED)).isTrue();
    }
}
