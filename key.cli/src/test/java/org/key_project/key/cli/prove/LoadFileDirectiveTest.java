/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.io.StringWriter;
import java.util.Objects;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import org.key_project.key.cli.Log;
import org.key_project.key.cli.Main;
import org.key_project.key.cli.ProtocolWriter;
import org.key_project.key.cli.ResultRecordWriter;
import org.key_project.key.cli.Verbosity;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for the load-file selection surfaces of §4.2 of the headless interface spec:
 * {@code \chooseContract} and {@code \proofObligation} with a plain canonical contract name.
 * <p>
 * A load-file directive selects exactly that contract when no {@code --choose-contract} option
 * is given; CLI selectors take precedence over the load file.
 */
class LoadFileDirectiveTest {

    private static final String ONE_NAME = "C[C::one()].JML normal_behavior operation contract.0";
    private static final String TWO_NAME = "C[C::two()].JML normal_behavior operation contract.0";

    @BeforeAll
    static void quietLogs() {
        Log.configureLogging(Verbosity.ERROR);
    }

    @Test
    @Timeout(300)
    void chooseContractLoadsTheNamedContract() throws ProblemLoaderException {
        KeYEnvironment<?> environment = KeYEnvironment.load(Fixtures.chooseKey());
        try {
            assertThat(contractNameOfLoadedProof(environment)).isEqualTo(ONE_NAME);
        } finally {
            environment.dispose();
        }
    }

    @Test
    @Timeout(300)
    void proofObligationLoadsTheNamedContract() throws ProblemLoaderException {
        KeYEnvironment<?> environment = KeYEnvironment.load(Fixtures.proofObligationKey());
        try {
            assertThat(contractNameOfLoadedProof(environment)).isEqualTo(ONE_NAME);
        } finally {
            environment.dispose();
        }
    }

    @Test
    @Timeout(300)
    void proveWithChooseContractDirectiveProvesExactlyThatContract() {
        Run run = run("prove", Fixtures.chooseKey().toString());

        assertThat(run.exit()).isZero();
        assertThat(run.resultLines()).hasSize(1);
        assertThat(run.out()).contains("\"contract\":\"" + ONE_NAME + "\"");
        assertThat(run.out()).contains("\"status\":\"closed\"");
    }

    @Test
    @Timeout(300)
    void proveWithProofObligationDirectiveProvesExactlyThatContract() {
        Run run = run("prove", Fixtures.proofObligationKey().toString());

        assertThat(run.exit()).isZero();
        assertThat(run.resultLines()).hasSize(1);
        assertThat(run.out()).contains("\"contract\":\"" + ONE_NAME + "\"");
        assertThat(run.out()).contains("\"status\":\"closed\"");
    }

    @Test
    @Timeout(300)
    void commandLineSelectorTakesPrecedenceOverTheLoadFile() {
        Run run = run("prove", Fixtures.chooseKey().toString(), "--choose-contract", TWO_NAME);

        assertThat(run.exit()).isEqualTo(1);
        assertThat(run.resultLines()).hasSize(1);
        assertThat(run.out()).contains("\"contract\":\"" + TWO_NAME + "\"");
        assertThat(run.out()).contains("\"status\":\"open\"");
    }

    private static String contractNameOfLoadedProof(KeYEnvironment<?> environment) {
        Proof loaded = environment.getLoadedProof();
        assertThat(loaded).isNotNull();
        ProofOblInput po = Objects.requireNonNull(
            environment.getServices().getSpecificationRepository().getProofOblInput(loaded));
        assertThat(po).isInstanceOf(ContractPO.class);
        return ((ContractPO) po).getContract().getName();
    }

    private record Run(int exit, String out, String err) {
        java.util.List<String> resultLines() {
            return out.lines().filter(line -> line.startsWith(ResultRecordWriter.PREFIX)).toList();
        }
    }

    private static Run run(String... args) {
        StringWriter out = new StringWriter();
        StringWriter err = new StringWriter();
        var cli = Main.createCommandLine();
        cli.setOut(new ProtocolWriter(out));
        cli.setErr(new ProtocolWriter(err));
        int exit = cli.execute(args);
        return new Run(exit, out.toString(), err.toString());
    }
}
