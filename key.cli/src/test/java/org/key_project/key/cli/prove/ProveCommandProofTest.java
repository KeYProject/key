/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.io.StringWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.UUID;

import org.key_project.key.cli.Log;
import org.key_project.key.cli.Main;
import org.key_project.key.cli.ProtocolWriter;
import org.key_project.key.cli.ResultRecordWriter;
import org.key_project.key.cli.Verbosity;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.io.TempDir;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for the proof-file honesty of the {@code prove} subcommand (§3 of the headless interface
 * spec): a proof file is written only where the caller requested one ({@code --proof} or
 * {@code --proof-dir}), always for a closed proof (marker {@code // KEY_PROOF_STATUS closed 0}) and
 * for an unclosed proof only with {@code --save-partial} (marker
 * {@code // KEY_PROOF_STATUS open <n>}). An unwritable requested path, and proof output together
 * with several load files, are input errors (exit {@code 3}).
 */
class ProveCommandProofTest {

    private static final String ONE_NAME = "C[C::one()].JML normal_behavior operation contract.0";
    private static final String TWO_NAME = "C[C::two()].JML normal_behavior operation contract.0";

    @TempDir
    @SuppressWarnings("initialization.field.uninitialized") // JUnit injects the temp dir
    Path tmp;

    @BeforeAll
    static void quietLogs() {
        Log.configureLogging(Verbosity.ERROR);
    }

    @Test
    @Timeout(300)
    void openWithoutSavePartialWritesNothing() {
        Path proof = tmp.resolve("two.proof");
        Run run = run("prove", Fixtures.indexKey().toString(), "--choose-contract", TWO_NAME,
            "--proof", proof.toString());

        assertThat(run.exit()).isEqualTo(1);
        assertThat(Files.exists(proof)).isFalse();
        assertThat(run.resultLines()).hasSize(1);
        assertThat(run.resultLines().get(0)).contains("\"proofFile\":null");
    }

    @Test
    @Timeout(300)
    void openWithSavePartialWritesOpenMarker() throws Exception {
        Path proof = tmp.resolve("two.proof");
        Run run = run("prove", Fixtures.indexKey().toString(), "--choose-contract", TWO_NAME,
            "--proof", proof.toString(), "--save-partial");

        assertThat(run.exit()).isEqualTo(1);
        assertThat(Files.exists(proof)).isTrue();
        List<String> lines = Files.readAllLines(proof);
        assertThat(lines.get(0)).startsWith("// KEY_PROOF_STATUS open ");
        int openGoals = Integer.parseInt(
            lines.get(0).substring("// KEY_PROOF_STATUS open ".length()));
        assertThat(openGoals).isGreaterThanOrEqualTo(1);
        assertThat(run.resultLines().get(0))
                .contains(
                    "\"proofFile\":\"" + jsonPath(proof.toAbsolutePath().normalize()) + "\"");
    }

    @Test
    @Timeout(300)
    void proofWithBareRelativePathIsWritten() throws Exception {
        // a single-segment relative path has no parent directory: the saver must still work
        Path relative = Path.of("key-cli-relative-" + UUID.randomUUID() + ".proof");
        try {
            Run run = run("prove", Fixtures.indexKey().toString(), "--choose-contract", ONE_NAME,
                "--proof", relative.toString());

            assertThat(run.exit()).isZero();
            assertThat(run.err()).doesNotContain("KEY_ERROR");
            assertThat(Files.readAllLines(relative).get(0))
                    .isEqualTo("// KEY_PROOF_STATUS closed 0");
            assertThat(Files.readString(relative)).contains("\\proof");
            assertThat(run.resultLines().get(0))
                    .contains("\"proofFile\":\"" + jsonPath(relative.toAbsolutePath().normalize())
                        + "\"");
        } finally {
            Files.deleteIfExists(relative);
        }
    }

    @Test
    @Timeout(300)
    void closedWritesClosedMarker() throws Exception {
        Path proof = tmp.resolve("one.proof");
        Run run = run("prove", Fixtures.indexKey().toString(), "--choose-contract", ONE_NAME,
            "--proof", proof.toString());

        assertThat(run.exit()).isZero();
        assertThat(Files.exists(proof)).isTrue();
        List<String> lines = Files.readAllLines(proof);
        assertThat(lines.get(0)).isEqualTo("// KEY_PROOF_STATUS closed 0");
        // exactly one marker line in the whole file
        long count = lines.stream().filter("// KEY_PROOF_STATUS closed 0"::equals).count();
        assertThat(count).isEqualTo(1);
        assertThat(run.resultLines().get(0))
                .contains(
                    "\"proofFile\":\"" + jsonPath(proof.toAbsolutePath().normalize()) + "\"");
    }

    @Test
    @Timeout(300)
    void closedWithoutProofOptionsWritesNothing() throws Exception {
        Run run = run("prove", Fixtures.indexKey().toString(), "--choose-contract", ONE_NAME);

        assertThat(run.exit()).isZero();
        assertThat(run.resultLines()).hasSize(1);
        assertThat(run.resultLines().get(0)).contains("\"proofFile\":null");
        // no .proof file appeared in the run directory (the working directory)
        try (var stream = Files.list(Path.of("."))) {
            assertThat(stream.filter(path -> path.toString().endsWith(".proof"))).isEmpty();
        }
    }

    @Test
    @Timeout(300)
    void proofWithMultipleSelectedContractsIsAnInputError() {
        Run run = run("prove", Fixtures.indexKey().toString(), "--choose-contract", ONE_NAME,
            "--choose-contract", TWO_NAME, "--proof", tmp.resolve("x.proof").toString());

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err()).contains("KEY_ERROR");
        assertThat(run.resultLines()).isEmpty();
    }

    @Test
    @Timeout(300)
    void unwritableProofPathIsAnInputError() throws Exception {
        // a regular file where the parent directory of the proof should be
        Path blocker = tmp.resolve("blocked");
        Files.writeString(blocker, "not a directory");
        Path proof = blocker.resolve("x.proof");

        Run run = run("prove", Fixtures.indexKey().toString(), "--choose-contract", ONE_NAME,
            "--proof", proof.toString());

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err()).contains("cannot write proof");
        // the run must not report a success record while the requested proof is missing
        assertThat(run.resultLines()).isEmpty();
        assertThat(run.out()).doesNotContain("\"status\":\"closed\"");
    }

    @Test
    @Timeout(300)
    void proofWithTwoLoadFilesIsAnInputError() {
        Run run = run("prove", Fixtures.indexKey().toString(), Fixtures.overflowKey().toString(),
            "--proof", tmp.resolve("x.proof").toString());

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err()).contains("KEY_ERROR");
        assertThat(run.err()).contains("single load file");
        assertThat(run.resultLines()).isEmpty();
    }

    @Test
    @Timeout(300)
    void proofDirWithTwoLoadFilesIsAnInputError() {
        Run run = run("prove", Fixtures.indexKey().toString(), Fixtures.indexKey().toString(),
            "--proof-dir", tmp.resolve("dir").toString());

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err()).contains("KEY_ERROR");
        assertThat(run.err()).contains("single load file");
        assertThat(run.resultLines()).isEmpty();
    }

    @Test
    @Timeout(300)
    void proofAndProofDirAreMutuallyExclusive() {
        Run run = run("prove", Fixtures.indexKey().toString(), "--choose-contract", ONE_NAME,
            "--proof", tmp.resolve("a.proof").toString(), "--proof-dir",
            tmp.resolve("dir").toString());

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err()).contains("KEY_ERROR");
        assertThat(run.resultLines()).isEmpty();
    }

    @Test
    @Timeout(300)
    void proofDirNamesFilesBySelectionPosition() throws Exception {
        Path dir = tmp.resolve("proofs");
        // selection order is the command-line order: two() (open) first, one() (closed) second
        Run run = run("prove", Fixtures.indexKey().toString(), "--choose-contract", TWO_NAME,
            "--choose-contract", ONE_NAME, "--proof-dir", dir.toString(), "--save-partial");

        assertThat(run.exit()).isEqualTo(1);
        assertThat(Files.exists(dir.resolve("0.proof"))).isTrue();
        assertThat(Files.exists(dir.resolve("1.proof"))).isTrue();
        assertThat(Files.readAllLines(dir.resolve("0.proof")).get(0))
                .startsWith("// KEY_PROOF_STATUS open ");
        assertThat(Files.readAllLines(dir.resolve("1.proof")).get(0))
                .isEqualTo("// KEY_PROOF_STATUS closed 0");
        assertThat(run.resultLines()).hasSize(2);
        assertThat(run.resultLines().get(0))
                .contains("\"proofFile\":\""
                    + jsonPath(dir.resolve("0.proof").toAbsolutePath().normalize()) + "\"");
        assertThat(run.resultLines().get(1))
                .contains("\"proofFile\":\""
                    + jsonPath(dir.resolve("1.proof").toAbsolutePath().normalize()) + "\"");
    }

    private record Run(int exit, String out, String err) {
        List<String> resultLines() {
            return out.lines().filter(line -> line.startsWith(ResultRecordWriter.PREFIX)).toList();
        }
    }

    /// The path as rendered in the JSON result record, i.e. with backslashes and quotes escaped.
    private static String jsonPath(Path path) {
        return path.toString().replace("\\", "\\\\").replace("\"", "\\\"");
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
