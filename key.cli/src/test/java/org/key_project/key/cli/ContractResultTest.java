/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli;

import java.nio.file.Path;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Tests for the {@link ContractResult} record.
 */
class ContractResultTest {

    @Test
    void accessorsReturnConstructorArguments() {
        Path proofFile = Path.of("/tmp/x.proof");
        ContractResult result =
            new ContractResult("c1", ResultStatus.OPEN, 3, 17, proofFile, 2, 1, "oops");

        assertThat(result.contract()).isEqualTo("c1");
        assertThat(result.status()).isEqualTo(ResultStatus.OPEN);
        assertThat(result.openGoals()).isEqualTo(3);
        assertThat(result.elapsedMs()).isEqualTo(17);
        assertEquals(proofFile, result.proofFile());
        assertThat(result.smtCalls()).isEqualTo(2);
        assertThat(result.smtProved()).isEqualTo(1);
        assertEquals("oops", result.errorMessage());
    }

    @Test
    void allowsNullableProofFileAndErrorMessage() {
        ContractResult result =
            new ContractResult("c1", ResultStatus.CLOSED, 0, 0, null, 0, 0, null);

        assertNull(result.proofFile());
        assertNull(result.errorMessage());
    }

    @Test
    void implementsValueEquality() {
        ContractResult a =
            new ContractResult("c1", ResultStatus.CLOSED, 0, 1, null, 0, 0, null);
        ContractResult b =
            new ContractResult("c1", ResultStatus.CLOSED, 0, 1, null, 0, 0, null);
        ContractResult c =
            new ContractResult("c2", ResultStatus.CLOSED, 0, 1, null, 0, 0, null);

        assertThat(a).isEqualTo(b).hasSameHashCodeAs(b).isNotEqualTo(c);
    }
}
