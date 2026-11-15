/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.util.List;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.Contract;

import org.key_project.key.cli.CliError;
import org.key_project.key.cli.ContractResult;
import org.key_project.key.cli.ExitCode;
import org.key_project.key.cli.ResultRecordWriter;
import org.key_project.key.cli.ResultStatus;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.catchThrowableOfType;

/**
 * Tests for the classification of an exception thrown inside a single contract's proof attempt:
 * the contract gets a {@code "status":"error"} record with a non-{@code null}
 * {@code errorMessage}, and the run's worst exit code is the internal-error code 4 (§1).
 * <p>
 * A {@link ProofInputException} while creating the proof obligation is an <em>input</em> error
 * (§1 exit 3), not an internal one: {@link HeadlessProver#createProof} signals it with an
 * {@link ObligationCreationException}, which both subcommands report as a
 * {@code "status":"error"} record plus an input {@link CliError} (a {@code KEY_ERROR} line).
 */
class HeadlessProverErrorClassificationTest {

    private static final String CONTRACT = "C[C::two()].JML normal_behavior operation contract.0";

    @Test
    @Timeout(300)
    void proofInputExceptionIsAnInputErrorWithAnErrorRecord() throws Exception {
        try (KeYEnvironment<DefaultUserInterfaceControl> env =
            KeYEnvironment.load(Fixtures.indexKey())) {
            Contract contract = ContractIndex.fromEnvironment(env).byName(CONTRACT).orElseThrow();

            ObligationCreationException error = catchThrowableOfType(
                () -> HeadlessProver.createProof(failingEnvironment(env), contract),
                ObligationCreationException.class);

            assertThat(error).as("createProof must throw an ObligationCreationException")
                    .isNotNull();
            assertThat(error.contract()).isEqualTo(CONTRACT);
            // it classifies as an input error (exit 3), not an internal error (exit 4)
            assertThat(error.cliError().kind()).isEqualTo(CliError.Kind.INPUT);
            assertThat(requireMessage(error.cliError()))
                    .isEqualTo("cannot create the proof obligation for '" + CONTRACT
                        + "': boom");
            // and it carries a status-error record with a non-null errorMessage
            ContractResult record = error.record();
            assertThat(record.contract()).isEqualTo(CONTRACT);
            assertThat(record.status()).isEqualTo(ResultStatus.ERROR);
            assertThat(requireMessage(record)).isNotEmpty();
            String line = new ResultRecordWriter().toJsonLine(record);
            assertThat(line).startsWith(ResultRecordWriter.PREFIX)
                    .contains(CONTRACT)
                    .contains("\"status\":\"error\"")
                    .containsPattern("\"errorMessage\":\"[^\"]+\"");
            assertThat(line).doesNotContain("\"errorMessage\":null");
        }
    }

    /**
     * An environment whose {@code createProof} fails with a {@link ProofInputException},
     * simulating a load file whose obligation KeY cannot turn into a proof; everything else is
     * taken from the given environment.
     */
    private static KeYEnvironment<DefaultUserInterfaceControl> failingEnvironment(
            KeYEnvironment<DefaultUserInterfaceControl> delegate) {
        return new KeYEnvironment<DefaultUserInterfaceControl>(delegate.getUi(),
            delegate.getInitConfig()) {
            @Override
            public Proof createProof(ProofOblInput input) throws ProofInputException {
                throw new ProofInputException("boom");
            }
        };
    }

    @Test
    void errorResultCarriesStatusErrorAndMessage() {
        ContractResult result =
            HeadlessProver.errorResult(CONTRACT, 42, new RuntimeException("boom"));

        assertThat(result.contract()).isEqualTo(CONTRACT);
        assertThat(result.status()).isEqualTo(ResultStatus.ERROR);
        assertThat(result.openGoals()).isZero();
        assertThat(result.elapsedMs()).isEqualTo(42);
        assertThat(result.smtCalls()).isZero();
        assertThat(result.smtProved()).isZero();
        assertThat(requireMessage(result)).isEqualTo("boom");
    }

    @Test
    void errorResultWithoutMessageFallsBackToTheExceptionName() {
        ContractResult result =
            HeadlessProver.errorResult(CONTRACT, 0, new NullPointerException());

        assertThat(requireMessage(result)).isEqualTo("NullPointerException");
    }

    @Test
    void errorRecordRendersANonNullErrorMessage() {
        ContractResult result =
            HeadlessProver.errorResult(CONTRACT, 0, new RuntimeException("boom"));
        String line = new ResultRecordWriter().toJsonLine(result);

        assertThat(line).startsWith(ResultRecordWriter.PREFIX);
        assertThat(line).contains("\"status\":\"error\"");
        assertThat(line).containsPattern("\"errorMessage\":\"[^\"]+\"");
        assertThat(line).doesNotContain("\"errorMessage\":null");
    }

    @Test
    void worstExitCodeOfARunWithAnErrorIsInternalError() {
        ContractResult closed =
            new ContractResult("a", ResultStatus.CLOSED, 0, 0, null, 0, 0, null);
        ContractResult open = new ContractResult("b", ResultStatus.OPEN, 1, 0, null, 0, 0, null);
        ContractResult timedOut =
            new ContractResult("t", ResultStatus.TIMED_OUT, 1, 0, null, 0, 0, null);
        ContractResult error = HeadlessProver.errorResult(CONTRACT, 0, new RuntimeException("x"));

        assertThat(ExitCode.worstOf(List.of(closed, error)))
                .isEqualTo(ExitCode.INTERNAL_ERROR);
        assertThat(ExitCode.worstOf(List.of(open, error))).isEqualTo(ExitCode.INTERNAL_ERROR);
        assertThat(ExitCode.worstOf(List.of(timedOut, error)))
                .isEqualTo(ExitCode.INTERNAL_ERROR);
        assertThat(ExitCode.worstOf(List.of(error))).isEqualTo(ExitCode.INTERNAL_ERROR);
        // the error must win over every other status, i.e. the run exits 4
        assertThat(ExitCode.worstOf(List.of(closed, open, timedOut, error)).code())
                .isEqualTo(4);
    }

    private static String requireMessage(ContractResult result) {
        String message = result.errorMessage();
        if (message == null) {
            throw new AssertionError("expected a non-null errorMessage");
        }
        return message;
    }

    private static String requireMessage(Throwable error) {
        String message = error.getMessage();
        if (message == null) {
            throw new AssertionError("expected a non-null message");
        }
        return message;
    }
}
