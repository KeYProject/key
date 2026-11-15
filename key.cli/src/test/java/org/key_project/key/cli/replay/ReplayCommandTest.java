/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.replay;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import org.key_project.key.cli.Log;
import org.key_project.key.cli.Main;
import org.key_project.key.cli.Verbosity;
import org.key_project.key.cli.prove.Fixtures;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.io.TempDir;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for the {@code replay} subcommand (§7.2 of the headless interface spec): a saved proof
 * file is re-checked against its sources. The first-line status marker decides for
 * header-carrying files ({@code KEY_PROOF_STATUS open <n>} wins, {@code KEY_PROOF_STATUS closed
 * 0} must be confirmed by the internal replay); without a marker, {@code proof.closed()}
 * decides.
 */
class ReplayCommandTest {

    private static final String ONE_NAME = "C[C::one()].JML normal_behavior operation contract.0";
    private static final String TWO_NAME = "C[C::two()].JML normal_behavior operation contract.0";

    @TempDir
    Path tmp;

    @BeforeAll
    static void quietLogs() {
        Log.configureLogging(Verbosity.ERROR);
    }

    /**
     * Proves the closed {@code one()} contract and saves it to {@code tmp/one.proof} with the
     * {@code KEY_PROOF_STATUS closed 0} marker.
     */
    private Path saveClosedProof() {
        Path proof = tmp.resolve("one.proof");
        Run saved = run("prove", Fixtures.indexKey().toString(), "--choose-contract", ONE_NAME,
            "--proof", proof.toString());
        assertThat(saved.exit()).isZero();
        assertThat(Files.exists(proof)).isTrue();
        return proof;
    }

    private static List<String> lines(Path file) throws Exception {
        return Files.readAllLines(file);
    }

    private static Path rewriteFirstLine(Path file, String newFirstLine) throws Exception {
        List<String> lines = lines(file);
        lines.set(0, newFirstLine);
        // the rewritten file must keep the .proof extension to be loadable
        Path rewritten = file.resolveSibling("rewritten-" + file.getFileName());
        Files.writeString(rewritten, String.join("\n", lines) + "\n");
        return rewritten;
    }

    @Test
    @Timeout(300)
    void closedProofReplaysClosed() throws Exception {
        Path proof = saveClosedProof();
        assertThat(lines(proof).get(0)).isEqualTo("KEY_PROOF_STATUS closed 0");

        Run run = run("replay", proof.toString());

        assertThat(run.exit()).isZero();
        assertThat(run.lastLine()).isEqualTo("REPLAY closed 0");
    }

    @Test
    @Timeout(300)
    void openMarkerWinsOverClosedInternalReplay() throws Exception {
        // G2: the same (internally closed) proof with the header swapped to open 3
        Path proof = rewriteFirstLine(saveClosedProof(), "KEY_PROOF_STATUS open 3");

        Run run = run("replay", proof.toString());

        assertThat(run.exit()).isEqualTo(1);
        assertThat(run.lastLine()).isEqualTo("REPLAY unclosed 3");
    }

    @Test
    @Timeout(300)
    void withoutMarkerTheInternalStateDecides() throws Exception {
        Path proof = saveClosedProof();
        List<String> lines = lines(proof);
        lines.remove(0);
        Path noMarker = proof.resolveSibling("no-marker.proof");
        Files.writeString(noMarker, String.join("\n", lines) + "\n");

        Run run = run("replay", noMarker.toString());

        assertThat(run.exit()).isZero();
        assertThat(run.lastLine()).isEqualTo("REPLAY closed 0");
    }

    @Test
    @Timeout(300)
    void oversizedOpenMarkerIsReportedAsMalformed() throws Exception {
        Path proof = rewriteFirstLine(saveClosedProof(), "KEY_PROOF_STATUS open 99999999999");

        Run run = run("replay", proof.toString());

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.lastLine()).startsWith("REPLAY incompatible malformed status marker");
    }

    @Test
    void corruptFileIsIncompatible() throws Exception {
        Path proof = tmp.resolve("garbage.proof");
        Files.writeString(proof, "this is not a KeY proof file\n");

        Run run = run("replay", proof.toString());

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.lastLine()).startsWith("REPLAY incompatible");
    }

    @Test
    void missingFileIsIncompatible() {
        Run run = run("replay", tmp.resolve("nowhere.proof").toString());

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.lastLine()).startsWith("REPLAY incompatible");
    }

    @Test
    @Timeout(300)
    void closedMarkerButUnclosedProofIsIncompatible() throws Exception {
        // strip the \proof block: the marker still says closed, the replayed proof is not
        Path proof = saveClosedProof();
        List<String> lines = lines(proof);
        int proofBlock = lines.indexOf("\\proof {");
        assertThat(proofBlock).isGreaterThan(0);
        Path noSteps = proof.resolveSibling("no-steps.proof");
        Files.writeString(noSteps, String.join("\n", lines.subList(0, proofBlock)) + "\n");

        Run run = run("replay", noSteps.toString());

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.lastLine()).startsWith("REPLAY incompatible");
    }

    @Test
    @Timeout(300)
    void changedSourcesMakeTheClosedMarkerReplayIncompatible() throws Exception {
        // foreign proof: the sources the proof file refers to have changed, so the stored steps
        // no longer replay
        Path dir = tmp.resolve("fixture");
        Files.createDirectories(dir);
        Path indexKey = dir.resolve("index.key");
        Path cJava = dir.resolve("C.java");
        Files.copy(Fixtures.indexKey(), indexKey);
        Files.copy(Fixtures.indexKey().resolveSibling("C.java"), cJava);

        Path proof = dir.resolve("one.proof");
        Run saved = run("prove", indexKey.toString(), "--choose-contract", ONE_NAME, "--proof",
            proof.toString());
        assertThat(saved.exit()).isZero();

        // change the contract of one(): the stored proof of the old contract cannot replay
        Files.writeString(cJava,
            Files.readString(cJava).replace("ensures \\result == 1;", "ensures \\result == 2;"));

        Run run = run("replay", proof.toString());

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.lastLine()).startsWith("REPLAY incompatible");
    }

    @Test
    @Timeout(300)
    void contractFilterAcceptsMatchingName() throws Exception {
        Path proof = saveClosedProof();

        Run run = run("replay", proof.toString(), "--contract", ONE_NAME);

        assertThat(run.exit()).isZero();
        assertThat(run.lastLine()).isEqualTo("REPLAY closed 0");
    }

    @Test
    @Timeout(300)
    void contractFilterRejectsMismatchedName() throws Exception {
        Path proof = saveClosedProof();

        Run run = run("replay", proof.toString(), "--contract", TWO_NAME);

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.lastLine()).startsWith("REPLAY incompatible");
    }

    private record Run(int exit, String out, String err) {
        String lastLine() {
            List<String> lines = out.lines().toList();
            return lines.isEmpty() ? "" : lines.get(lines.size() - 1);
        }
    }

    private static Run run(String... args) {
        StringWriter out = new StringWriter();
        StringWriter err = new StringWriter();
        var cli = Main.createCommandLine();
        cli.setOut(new PrintWriter(out));
        cli.setErr(new PrintWriter(err));
        int exit = cli.execute(args);
        return new Run(exit, out.toString(), err.toString());
    }
}
