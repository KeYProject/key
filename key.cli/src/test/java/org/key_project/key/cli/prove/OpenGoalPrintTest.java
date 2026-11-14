/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;

import org.key_project.key.cli.Main;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import picocli.CommandLine;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Acceptance tests for the {@code --print-open-goals} open-goal output of the {@code prove}
 * subcommand (§6 of the headless interface spec):
 *
 * <ul>
 * <li>F1: two runs on the same open contract print byte-identical open-goal sections.</li>
 * <li>F2: for the known-open {@code Size} contract every printed formula is non-empty and
 * every position path matches {@code ^[1-9][0-9.]*$}.</li>
 * <li>{@code --print-open-goals 1} on a contract with two open goals prints one GOAL block
 * while {@code OPEN-GOAL-COUNT} keeps the true total.</li>
 * <li>Determinism (F1) also holds with {@code --no-truncate-formulas}.</li>
 * </ul>
 */
class OpenGoalPrintTest {

    private static final String TWO = "C[C::two()].JML normal_behavior operation contract.0";

    private static final String SIZE =
        "Size[Size::size(int)].JML normal_behavior operation contract.0";

    @BeforeAll
    static void quietLogs() {
        org.key_project.key.cli.Log.configureLogging(org.key_project.key.cli.Verbosity.ERROR);
    }

    /**
     * The outcome of one in-process CLI invocation.
     *
     * @param exit the process exit code
     * @param out everything written to stdout
     * @param err everything written to stderr
     */
    private record Run(int exit, String out, String err) {
    }

    private static Run run(String... args) {
        StringWriter out = new StringWriter();
        StringWriter err = new StringWriter();
        CommandLine cli = Main.createCommandLine();
        cli.setOut(new PrintWriter(out));
        cli.setErr(new PrintWriter(err));
        int exit = cli.execute(args);
        return new Run(exit, out.toString(), err.toString());
    }

    /**
     * Extracts the open-goal section of a stdout capture: from the first
     * {@code OPEN-GOAL-COUNT} line up to the line before the first {@code KEY_RESULT} line
     * (inclusive of the terminating blank line).
     */
    static String openGoalSection(String out) {
        int start = out.indexOf("OPEN-GOAL-COUNT ");
        if (start < 0) {
            return "";
        }
        int end = out.indexOf("\nKEY_RESULT ", start);
        return end < 0 ? out.substring(start) : out.substring(start, end + 1);
    }

    /**
     * Splits an open-goal section into its {@code GOAL} blocks; each block spans from its
     * {@code GOAL <id> <position-path>} header line to the next {@code GOAL} header (or the
     * end of the section) and includes its terminating blank line.
     */
    static List<String> goalBlocks(String section) {
        List<String> blocks = new ArrayList<>();
        StringBuilder current = new StringBuilder();
        for (String line : section.split("\n", -1)) {
            if (line.startsWith("GOAL ")) {
                if (current.length() > 0) {
                    blocks.add(current.toString());
                }
                current = new StringBuilder(line);
            } else if (current.length() > 0) {
                current.append('\n').append(line);
            }
        }
        if (current.length() > 0) {
            blocks.add(current.toString());
        }
        return blocks;
    }

    private static String lastLine(String out) {
        String trimmed = out.stripTrailing();
        int idx = trimmed.lastIndexOf('\n');
        return idx < 0 ? trimmed : trimmed.substring(idx + 1);
    }

    private static void checkBlock(String block, int expectedId) {
        String[] lines = block.split("\n", -1);
        String[] header = lines[0].split("\\s+");
        assertThat(header).hasSize(3);
        assertThat(header[0]).isEqualTo("GOAL");
        assertThat(header[1]).isEqualTo(String.valueOf(expectedId));
        assertThat(header[2]).matches("[1-9][0-9.]*");
        // every formula line: two-space indent, non-empty, up to the terminating blank line
        int formulaLines = 0;
        for (int i = 1; i < lines.length; i++) {
            if (lines[i].isEmpty()) {
                break;
            }
            assertThat(lines[i]).startsWith("  ");
            assertThat(lines[i].trim()).isNotEmpty();
            formulaLines++;
        }
        assertThat(formulaLines).isGreaterThanOrEqualTo(1);
        assertThat(lines[lines.length - 1]).isEmpty();
    }

    @Test
    @Timeout(300)
    void f1TwoRunsOnSameOpenContractAreByteIdentical() {
        String[] args =
            {"prove", Fixtures.indexKey().toString(), "--choose-contract", TWO, "--print-open-goals"};
        Run first = run(args);
        Run second = run(args);

        assertThat(first.exit()).isEqualTo(1);
        assertThat(second.exit()).isEqualTo(1);
        String section = openGoalSection(first.out());
        assertThat(section).isNotEmpty();
        assertThat(section).startsWith("OPEN-GOAL-COUNT 1\n");
        assertThat(section).isEqualTo(openGoalSection(second.out()));
        List<String> blocks = goalBlocks(section);
        assertThat(blocks).hasSize(1);
        checkBlock(blocks.get(0), 0);
        // the KEY_RESULT line is still the last line of stdout
        assertThat(lastLine(first.out())).startsWith("KEY_RESULT ");
    }

    @Test
    @Timeout(300)
    void f2SizeContractFormulasNonEmptyAndPathsMatchRegex() {
        Run result = run("prove", Fixtures.sizeOpenKey().toString(), "--choose-contract", SIZE,
            "--print-open-goals");

        assertThat(result.exit()).isEqualTo(1);
        String section = openGoalSection(result.out());
        assertThat(section).startsWith("OPEN-GOAL-COUNT 2\n");
        List<String> blocks = goalBlocks(section);
        assertThat(blocks).hasSize(2);
        checkBlock(blocks.get(0), 0);
        checkBlock(blocks.get(1), 1);
        assertThat(lastLine(result.out())).startsWith("KEY_RESULT ");
    }

    @Test
    @Timeout(300)
    void maxTruncatesGoalBlocksButCountStaysTrue() {
        Run result = run("prove", Fixtures.sizeOpenKey().toString(), "--choose-contract", SIZE,
            "--print-open-goals", "1");

        assertThat(result.exit()).isEqualTo(1);
        String section = openGoalSection(result.out());
        assertThat(section).startsWith("OPEN-GOAL-COUNT 2\n");
        List<String> blocks = goalBlocks(section);
        assertThat(blocks).hasSize(1);
        checkBlock(blocks.get(0), 0);
    }

    @Test
    @Timeout(300)
    void noTruncateFormulasTwoRunsByteIdentical() {
        String[] args = {"prove", Fixtures.sizeOpenKey().toString(), "--choose-contract", SIZE,
            "--print-open-goals", "0", "--no-truncate-formulas"};
        Run first = run(args);
        Run second = run(args);

        assertThat(first.exit()).isEqualTo(1);
        String section = openGoalSection(first.out());
        assertThat(section).startsWith("OPEN-GOAL-COUNT 2\n");
        assertThat(goalBlocks(section)).hasSize(2);
        assertThat(section).isEqualTo(openGoalSection(second.out()));
    }
}
