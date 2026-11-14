/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import org.key_project.key.cli.ResultStatus;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Unit tests for the timeout decision of {@link HeadlessProver#classifyStatus}: the stop
 * condition's message cannot distinguish a timeout from reaching the maximal number of rule
 * applications, so the status must follow from the measured search time.
 */
class HeadlessProverStatusClassificationTest {

    @Test
    void closedProofIsClosedRegardlessOfTime() {
        assertThat(HeadlessProver.classifyStatus(true, 0, 0)).isEqualTo(ResultStatus.CLOSED);
        assertThat(HeadlessProver.classifyStatus(true, 30_000, 10_000))
                .isEqualTo(ResultStatus.CLOSED);
        assertThat(HeadlessProver.classifyStatus(true, 1, 1)).isEqualTo(ResultStatus.CLOSED);
    }

    @Test
    void unclosedWithoutTimeoutIsOpen() {
        assertThat(HeadlessProver.classifyStatus(false, 0, 10_000)).isEqualTo(ResultStatus.OPEN);
        assertThat(HeadlessProver.classifyStatus(false, 0, 0)).isEqualTo(ResultStatus.OPEN);
    }

    @Test
    void unclosedBelowTimeoutIsOpen() {
        // the strategy exhausted its rules before the timeout elapsed: "open", not "timed_out"
        assertThat(HeadlessProver.classifyStatus(false, 30_000, 29_999))
                .isEqualTo(ResultStatus.OPEN);
        assertThat(HeadlessProver.classifyStatus(false, 100, 99)).isEqualTo(ResultStatus.OPEN);
    }

    @Test
    void unclosedAtOrBeyondTimeoutIsTimedOut() {
        // the stop condition fires once elapsed >= timeout, so the measured time reaches the
        // bound exactly
        assertThat(HeadlessProver.classifyStatus(false, 30_000, 30_000))
                .isEqualTo(ResultStatus.TIMED_OUT);
        assertThat(HeadlessProver.classifyStatus(false, 1, 1)).isEqualTo(ResultStatus.TIMED_OUT);
        assertThat(HeadlessProver.classifyStatus(false, 1, 57)).isEqualTo(ResultStatus.TIMED_OUT);
    }
}
