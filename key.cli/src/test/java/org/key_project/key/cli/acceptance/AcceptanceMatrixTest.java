/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.acceptance;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.key_project.key.cli.Log;
import org.key_project.key.cli.Main;
import org.key_project.key.cli.ResultRecordWriter;
import org.key_project.key.cli.Verbosity;
import org.key_project.key.cli.prove.Fixtures;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * The §9 acceptance matrix as an executable test: each row spawns the CLI as a subprocess
 * ({@code java -cp <runtimeClasspath> org.key_project.key.cli.Main …}, isolated by a temp
 * {@code user.home} and a temp working directory) and asserts the exact exit code and the
 * stdout/stderr markers of the row.
 * <p>
 * The spec's flat invocations are mapped onto the subcommand CLI (deviation from §0, see the
 * Phase 7 brief): e.g. {@code --choose-contract '<NAME>'} becomes
 * {@code prove --choose-contract '<NAME>' <file>}, and {@code --list-contracts} becomes
 * {@code list <file>}.
 * <p>
 * Rows 7–9 exercise the Phase 5/6 features ({@code --proof}, {@code --save-partial},
 * {@code --print-open-goals}, the {@code replay} subcommand); all ten rows are active.
 */
class AcceptanceMatrixTest {

    /** Canonical name of the closed {@code one()} contract of the §9 fixture. */
    private static final String ONE_NAME =
        "C[C::one()].JML normal_behavior operation contract.0";
    /** Canonical name of the open {@code two()} contract of the §9 fixture. */
    private static final String TWO_NAME =
        "C[C::two()].JML normal_behavior operation contract.0";

    /// A tab-separated §4.3 listing line: {@code <IDX>\t<target>\t<NAME>}.
    private static final String LISTING_LINE =
        "\\d+\tC::[a-z]+\tC\\[C::[a-z]+\\(\\)\\]\\.JML normal_behavior operation contract\\."
            + "\\d+";

    // set in @BeforeAll setup()
    @SuppressWarnings("nullness:initialization.static.field.uninitialized")
    private static Path base;
    @SuppressWarnings("nullness:initialization.static.field.uninitialized")
    private static Path home;

    @BeforeAll
    @Timeout(300)
    @SuppressWarnings({ "nullness:initialization.field.uninitialized", "nullness:assignment" })
    static void setup() throws IOException {
        Log.configureLogging(Verbosity.ERROR);
        base = Files.createTempDirectory("key-cli-acceptance");
        home = base.resolve("home");
        Files.createDirectories(home);
    }

    /**
     * Row 1: selecting the closed {@code one()} contract by name proves it, exits {@code 0},
     * and prints one {@code KEY_RESULT} line (last line of stdout, B1) with
     * {@code "status":"closed"} and {@code "openGoals":0}.
     */
    @Test
    @Timeout(600)
    void row1_selectClosedContractExits0() throws IOException {
        Run run = run("prove", "--choose-contract", ONE_NAME, Fixtures.indexKey().toString());

        assertThat(run.exit()).isEqualTo(0);
        assertResultLinesAreLast(run);
        assertThat(run.resultLines()).hasSize(1);
        assertThat(run.resultLines().get(0))
                .contains("\"status\":\"closed\"", "\"openGoals\":0", "\"errorMessage\":null");
        assertNoSurpriseProofFiles(run.workDir());
    }

    /**
     * Row 2: selecting the open {@code two()} contract exits {@code 1} and prints one
     * {@code KEY_RESULT} line (last line of stdout, B1) with {@code "status":"open"} and
     * {@code "openGoals"} ≥ 1 (B2).
     */
    @Test
    @Timeout(600)
    void row2_selectOpenContractExits1() throws IOException {
        Run run = run("prove", "--choose-contract", TWO_NAME, Fixtures.indexKey().toString());

        assertThat(run.exit()).isEqualTo(1);
        assertResultLinesAreLast(run);
        assertThat(run.resultLines()).hasSize(1);
        assertThat(run.resultLines().get(0))
                .contains("\"status\":\"open\"")
                .containsPattern("\"openGoals\":([1-9][0-9]*)");
        // C1: an unclosed proof without --proof* must not write a .proof file anywhere
        assertNoSurpriseProofFiles(run.workDir());
    }

    /**
     * Row 3: {@code --timeout=1} without a selector proves all contracts; both searches are
     * abandoned by the timeout, so the exit is {@code 2} and both records report
     * {@code "status":"timed_out"}.
     */
    @Test
    @Timeout(600)
    void row3_allContractsTimeOut() throws IOException {
        Run run = run("prove", "--timeout=1", Fixtures.indexKey().toString());

        assertThat(run.exit()).isEqualTo(2);
        assertResultLinesAreLast(run);
        assertThat(run.resultLines()).hasSize(2);
        for (String line : run.resultLines()) {
            assertThat(line).contains("\"status\":\"timed_out\"");
        }
    }

    /**
     * Row 4: an unknown contract selector is an input error: exit {@code 3}, the stderr line
     * {@code KEY_ERROR contract 'NoSuch' not found}, and the full listing on stdout (no
     * {@code KEY_RESULT} line).
     */
    @Test
    @Timeout(600)
    void row4_unknownContractExits3WithListing() throws IOException {
        Run run = run("prove", "--choose-contract", "NoSuch", Fixtures.indexKey().toString());

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.errLines())
                .as("stderr: %s", run.errText())
                .contains("KEY_ERROR contract 'NoSuch' not found");
        assertThat(run.outLines()).hasSize(2);
        for (String line : run.outLines()) {
            assertThat(line).matches(LISTING_LINE);
        }
        assertThat(run.resultLines()).isEmpty();
    }

    /**
     * Row 5: {@code list} exits {@code 0} and prints at least two tab-separated lines of the
     * form {@code <IDX>\t<clazz>::<m>\t<NAME>}, and no {@code KEY_RESULT} line.
     */
    @Test
    @Timeout(600)
    void row5_listingIsTabSeparatedAndHasNoResultLine() throws IOException {
        Run run = run("list", Fixtures.indexKey().toString());

        assertThat(run.exit()).isEqualTo(0);
        assertThat(run.outLines()).as("stdout: %s", run.outText()).hasSizeGreaterThanOrEqualTo(2);
        for (String line : run.outLines()) {
            assertThat(line).matches(LISTING_LINE);
        }
        assertThat(run.outText()).doesNotContain(ResultRecordWriter.PREFIX);
    }

    /**
     * Row 6: a settings file citing an unknown key is an input error: exit {@code 3}, a
     * {@code KEY_ERROR settings: … not understood} line on stderr, nothing proven.
     */
    @Test
    @Timeout(600)
    void row6_unknownSettingsKeyExits3() throws IOException {
        Run run = run("prove", "--settings-file", Fixtures.acceptanceSettings().toString(),
            Fixtures.indexKey().toString());

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.errLines())
                .as("stderr: %s", run.errText())
                .anySatisfy(line -> assertThat(line)
                        .startsWith("KEY_ERROR settings:")
                        .contains("not understood"));
        assertThat(run.resultLines()).isEmpty();
    }

    /**
     * Row 7 (Phase 6): {@code --print-open-goals 5} on the open contract prints the open-goal
     * block (true count, ≤5 {@code GOAL} blocks) and exits {@code 1}.
     */
    @Test
    @Timeout(600)
    void row7_printOpenGoals() throws IOException {
        Run run = run("prove", "--print-open-goals", "5", "--choose-contract", TWO_NAME,
            Fixtures.indexKey().toString());

        assertThat(run.exit()).isEqualTo(1);
        assertThat(run.outLines())
                .as("stdout: %s", run.outText())
                .anySatisfy(line -> assertThat(line).matches("OPEN-GOAL-COUNT [1-9][0-9]*"));
        long goalBlocks =
            run.outLines().stream().filter(line -> line.startsWith("GOAL ")).count();
        assertThat(goalBlocks).as("stdout: %s", run.outText()).isBetween(1L, 5L);
    }

    /**
     * Row 8 (Phase 5/6): the proof of the closed contract written via {@code --proof} replays
     * as {@code REPLAY closed 0} with exit {@code 0}.
     */
    @Test
    @Timeout(900)
    void row8_replayClosedProof() throws IOException {
        Path proof = Files.createTempDirectory("key-cli-acceptance-row8").resolve("closed.proof");
        Run prove = run("prove", "--proof", proof.toString(), "--choose-contract", ONE_NAME,
            Fixtures.indexKey().toString());
        assertThat(prove.exit()).as("stderr: %s", prove.errText()).isEqualTo(0);
        assertThat(Files.exists(proof)).isTrue();

        Run replay = run("replay", proof.toString());
        assertThat(replay.exit()).as("stderr: %s", replay.errText()).isEqualTo(0);
        assertThat(replay.outLines()).contains("REPLAY closed 0");
    }

    /**
     * Row 9 (Phase 5/6): a partial proof saved via {@code --save-partial} replays as
     * {@code REPLAY unclosed <n>} with exit {@code 1}.
     */
    @Test
    @Timeout(900)
    void row9_replayPartialProof() throws IOException {
        Path proof = Files.createTempDirectory("key-cli-acceptance-row9").resolve("partial.proof");
        Run prove = run("prove", "--save-partial", "--proof", proof.toString(),
            "--choose-contract", TWO_NAME, Fixtures.indexKey().toString());
        assertThat(prove.exit()).as("stderr: %s", prove.errText()).isEqualTo(1);
        assertThat(Files.exists(proof)).isTrue();

        Run replay = run("replay", proof.toString());
        assertThat(replay.exit()).as("stderr: %s", replay.errText()).isEqualTo(1);
        assertThat(replay.outLines())
                .as("stdout: %s", replay.outText())
                .anySatisfy(line -> assertThat(line).matches("REPLAY unclosed [1-9][0-9]*"));
    }

    /**
     * Row 10 (§8/H1): each of the three bad-construct load files fails the run with exit
     * {@code 3} and exactly one {@code KEY_ERROR … construct '<snippet>' …} line on stderr —
     * the total count equals the number of bad constructs.
     */
    @Test
    @Timeout(900)
    void row10_badConstructsExits3WithKeyError() throws IOException {
        long totalKeyErrorLines = 0;
        for (Fixtures.BadConstruct bad : Fixtures.badConstructs()) {
            Run run = run("prove", bad.key().toString());
            assertThat(run.exit()).as("stderr: %s", run.errText()).isEqualTo(3);
            List<String> keyErrors = run.errLines().stream()
                    .filter(line -> line.startsWith("KEY_ERROR")).toList();
            assertThat(keyErrors).as("stderr: %s", run.errText()).hasSize(1);
            assertThat(keyErrors.get(0))
                    .contains("construct '" + bad.snippet() + "' not supported:");
            // never a crash: no NPE/CCE, no stack trace on stderr
            assertThat(run.errText()).doesNotContain("NullPointerException", "ClassCastException",
                "at de.uka");
            totalKeyErrorLines += keyErrors.size();
        }
        // H1: the KEY_ERROR line count equals the number of bad constructs
        assertThat(totalKeyErrorLines).isEqualTo(Fixtures.badConstructs().size());
    }

    /**
     * B1: all {@code KEY_RESULT} lines of stdout form a consecutive block at the very end
     * (no other line of stdout may start with the prefix).
     */
    private static void assertResultLinesAreLast(Run run) {
        List<String> out = run.outLines();
        int count = run.resultLines().size();
        assertThat(count).as("stdout: %s", run.outText()).isPositive();
        for (int i = out.size() - count; i < out.size(); i++) {
            assertThat(out.get(i)).as("stdout line %d", i)
                    .startsWith(ResultRecordWriter.PREFIX);
        }
    }

    /** C1: no {@code .proof} file was written anywhere under the run's working directory. */
    private static void assertNoSurpriseProofFiles(Path workDir) throws IOException {
        try (var paths = Files.walk(workDir)) {
            assertThat(paths.filter(it -> it.toString().endsWith(".proof")).count())
                    .as("unexpected proof files under %s", workDir)
                    .isZero();
        }
    }

    /** The outcome of one subprocess invocation. */
    private record Run(int exit, Path workDir, String outText, String errText) {

        List<String> outLines() {
            return outText.lines().filter(line -> !line.isEmpty()).toList();
        }

        List<String> errLines() {
            return errText.lines().filter(line -> !line.isEmpty()).toList();
        }

        List<String> resultLines() {
            return outLines().stream().filter(line -> line.startsWith(ResultRecordWriter.PREFIX))
                    .toList();
        }
    }

    /**
     * Spawns the CLI as a subprocess in a fresh working directory under the temp base, with
     * {@code user.home} isolated to the temp home, and waits for it to terminate.
     */
    private static Run run(String... args) throws IOException {
        Path workDir = Files.createTempDirectory(base, "run");
        List<String> command = new ArrayList<>();
        command.add(javaBin());
        command.add("-Duser.home=" + home);
        command.add("-cp");
        command.add(System.getProperty("java.class.path"));
        command.add(Main.class.getName());
        command.addAll(List.of(args));
        Process process =
            new ProcessBuilder(command).directory(workDir.toFile()).redirectErrorStream(false)
                    .start();
        String out = new String(process.getInputStream().readAllBytes(), StandardCharsets.UTF_8);
        String err = new String(process.getErrorStream().readAllBytes(), StandardCharsets.UTF_8);
        try {
            boolean finished = process.waitFor(480, TimeUnit.SECONDS);
            if (!finished) {
                process.destroyForcibly();
                throw new AssertionError("subprocess did not terminate: " + command);
            }
            return new Run(process.exitValue(), workDir, out, err);
        } catch (InterruptedException e) {
            process.destroyForcibly();
            Thread.currentThread().interrupt();
            throw new AssertionError("interrupted while waiting for the subprocess", e);
        }
    }

    private static String javaBin() {
        return Path.of(System.getProperty("java.home"), "bin", "java").toString();
    }
}
