/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.util.List;

import org.key_project.key.cli.ContractResult;
import org.key_project.key.cli.Log;
import org.key_project.key.cli.ResultRecordWriter;
import org.key_project.key.cli.ResultStatus;
import org.key_project.key.cli.Verbosity;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Slow but small test: loads the two-method fixture and proves all contracts with
 * {@link HeadlessProver}.
 */
class HeadlessProverTest {

    private static final String ONE_NAME = "C[C::one()].JML normal_behavior operation contract.0";
    private static final String TWO_NAME = "C[C::two()].JML normal_behavior operation contract.0";

    @BeforeAll
    static void quietLogs() {
        Log.configureLogging(Verbosity.ERROR);
    }

    @Test
    @Timeout(300)
    void provesAllContracts() throws Exception {
        List<ContractResult> results = new HeadlessProver().proveAll(Fixtures.indexKey());

        assertThat(results).hasSize(2);
        assertThat(results).extracting(ContractResult::contract)
                .containsExactly(ONE_NAME, TWO_NAME);

        assertThat(results).hasSize(2);
        assertThat(results).extracting(ContractResult::contract)
                .containsExactly(ONE_NAME, TWO_NAME);

        // results come back in the stable index order: one() = closed, two() = open
        ContractResult closed = results.get(0);
        ContractResult open = results.get(1);
        assertThat(closed.contract()).isEqualTo(ONE_NAME);
        assertThat(open.contract()).isEqualTo(TWO_NAME);

        assertThat(closed.status()).isEqualTo(ResultStatus.CLOSED);
        assertThat(closed.openGoals()).isZero();
        assertThat(closed.elapsedMs()).isGreaterThanOrEqualTo(0);
        assertNull(closed.errorMessage());

        assertThat(open.status()).isEqualTo(ResultStatus.OPEN);
        assertThat(open.openGoals()).isGreaterThanOrEqualTo(1);
        assertThat(open.elapsedMs()).isGreaterThanOrEqualTo(0);
        assertNull(open.errorMessage());

        // each contract renders exactly one KEY_RESULT line
        ResultRecordWriter writer = new ResultRecordWriter();
        for (ContractResult result : results) {
            assertThat(writer.toJsonLine(result)).startsWith(ResultRecordWriter.PREFIX + "{");
        }
    }
}
