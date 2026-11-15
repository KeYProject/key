/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli;

import java.nio.file.Path;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledOnOs;
import org.junit.jupiter.api.condition.OS;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Byte-exact tests for the {@code KEY_RESULT} line of {@link ResultRecordWriter} (§2 of the
 * headless interface contract).
 */
class ResultRecordWriterTest {

    private static final String QUICKHEAP_CONTRACT =
        "edu.kit.quickheap.QuickHeap[edu.kit.quickheap.QuickHeap::partition([I,int,int,[I)].JML "
            + "normal_behavior operation contract.0";

    private final ResultRecordWriter writer = new ResultRecordWriter();

    @Test
    void goldenClosedLine() {
        ContractResult result = new ContractResult(QUICKHEAP_CONTRACT, ResultStatus.CLOSED, 0,
            1234, null, 0, 0, null);

        String expected =
            """
                    KEY_RESULT {"version":1,"contract":"edu.kit.quickheap.QuickHeap[edu.kit.quickheap.QuickHeap::partition([I,int,int,[I)].JML normal_behavior operation contract.0","status":"closed","openGoals":0,"elapsedMs":1234,"proofFile":null,"smtCalls":0,"smtProved":0,"errorMessage":null}""";

        assertThat(writer.toJsonLine(result)).isEqualTo(expected);
    }

    @Test
    void goldenOpenLine() {
        ContractResult result =
            new ContractResult("C[C::two()].JML normal_behavior operation contract.0",
                ResultStatus.OPEN, 2, 42, null, 0, 0, null);

        String expected =
            """
                    KEY_RESULT {"version":1,"contract":"C[C::two()].JML normal_behavior operation contract.0","status":"open","openGoals":2,"elapsedMs":42,"proofFile":null,"smtCalls":0,"smtProved":0,"errorMessage":null}""";

        assertThat(writer.toJsonLine(result)).isEqualTo(expected);
    }

    @Test
    void goldenErrorLineWithEscapedMessage() {
        // message contains a quote and a backslash
        ContractResult result = new ContractResult(
            "C[C::f()].JML normal_behavior operation contract.0", ResultStatus.ERROR, 0, 5, null, 0,
            0, "msg: \"a\\b\"");

        String expected =
            """
                    KEY_RESULT {"version":1,"contract":"C[C::f()].JML normal_behavior operation contract.0","status":"error","openGoals":0,"elapsedMs":5,"proofFile":null,"smtCalls":0,"smtProved":0,"errorMessage":"msg: \\"a\\\\b\\""}""";

        assertThat(writer.toJsonLine(result)).isEqualTo(expected);
    }

    @Test
    void escapesQuotesBackslashesAndControlCharacters() {
        ContractResult result = new ContractResult("a\"b\\c\nd\te", ResultStatus.CLOSED, 0, 0, null,
            0, 0, null);

        String line = writer.toJsonLine(result);
        assertThat(line).contains("\"contract\":\"a\\\"b\\\\c\\nd\\te\"");
    }

    @Test
    void nullFieldsRenderAsLiteralNull() {
        ContractResult result =
            new ContractResult("c", ResultStatus.CLOSED, 0, 0, null, 0, 0, null);

        String line = writer.toJsonLine(result);
        assertThat(line).contains("\"proofFile\":null");
        assertThat(line).contains("\"errorMessage\":null");
    }

    // a path with a quote is impossible to construct on Windows; the escaping itself is
    // covered by escapesQuotesBackslashesAndControlCharacters on every platform
    @Test
    @EnabledOnOs({ OS.LINUX, OS.MAC })
    void proofFileIsRenderedAsEscapedString() {
        Path proofFile = Path.of("/tmp/out dir/a\"b.proof");
        ContractResult result =
            new ContractResult("c", ResultStatus.CLOSED, 0, 0, proofFile, 0, 0, null);

        String line = writer.toJsonLine(result);
        assertThat(line).contains("\"proofFile\":\"/tmp/out dir/a\\\"b.proof\"");
    }

    @Test
    void selectsCorrectSmtCounters() {
        ContractResult result =
            new ContractResult("c", ResultStatus.CLOSED, 0, 0, null, 7, 3, null);

        String line = writer.toJsonLine(result);
        assertThat(line).contains("\"smtCalls\":7");
        assertThat(line).contains("\"smtProved\":3");
    }
}
