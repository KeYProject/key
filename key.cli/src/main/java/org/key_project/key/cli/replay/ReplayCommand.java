/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.replay;

import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.concurrent.Callable;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader.ReplayResult;
import de.uka.ilkd.key.proof.io.ProofSaver;

import org.key_project.key.cli.ExitCode;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import picocli.CommandLine.Command;
import picocli.CommandLine.Model.CommandSpec;
import picocli.CommandLine.Option;
import picocli.CommandLine.Parameters;
import picocli.CommandLine.Spec;

/**
 * The {@code replay} subcommand (§7.2 of the headless interface spec): loads a saved proof file
 * (marker-tolerantly, since the first line may carry the {@code KEY_PROOF_STATUS} marker) and
 * re-checks it against the sources it refers to.
 * <p>
 * The subcommand prints exactly one of the following as the last line of stdout:
 * <ul>
 * <li>{@code REPLAY closed 0} (exit {@code 0})</li>
 * <li>{@code REPLAY unclosed <n>} (exit {@code 1})</li>
 * <li>{@code REPLAY incompatible <reason>} (exit {@code 3})</li>
 * </ul>
 * The marker rule of §3 decides for header-carrying files: a
 * {@code KEY_PROOF_STATUS open <n>} marker reports {@code REPLAY unclosed <n>} even if the
 * internal replay disagrees; a {@code KEY_PROOF_STATUS closed 0} marker must be confirmed by the
 * internal replay, otherwise the file is {@code incompatible}. Without a marker, the internal
 * state of the loaded proof decides. All load and replay errors are {@code incompatible}.
 * <p>
 * {@code --contract <NAME>} filters the loaded proof's obligation (§4.2): a mismatch is
 * {@code incompatible}. The root command's {@code --config-dir} option applies as well.
 */
@Command(name = "replay",
    description = "Re-check a saved proof file against its sources. Prints exactly one of "
        + "'REPLAY closed 0' (exit 0), 'REPLAY unclosed <n>' (exit 1) or "
        + "'REPLAY incompatible <reason>' (exit 3).",
    mixinStandardHelpOptions = true)
public final class ReplayCommand implements Callable<Integer> {

    private static final Logger LOGGER = LoggerFactory.getLogger(ReplayCommand.class);

    @Spec
    @SuppressWarnings("initialization.field.uninitialized")
    private CommandSpec spec;

    @Parameters(arity = "1", paramLabel = "<PROOF>",
        description = "Saved proof file (.proof) to re-check against its sources.")
    @SuppressWarnings("initialization.field.uninitialized")
    private Path proofFile;

    @Option(names = "--contract", paramLabel = "<NAME>",
        description = "Only accept the proof if its obligation has exactly this canonical "
            + "contract name (§4.2); a mismatch is reported as incompatible.")
    @org.jspecify.annotations.Nullable
    private String contract;

    /**
     * Replays the given proof file.
     *
     * @return the exit code: {@code 0} for {@code REPLAY closed 0}, {@code 1} for
     *         {@code REPLAY unclosed <n>}, {@code 3} for {@code REPLAY incompatible <reason>}
     */
    @Override
    public Integer call() {
        PrintWriter out = spec.commandLine().getOut();
        try {
            return replay(out);
        } catch (Exception e) {
            // §7.2: every load or replay failure is an incompatible proof (exit 3)
            LOGGER.debug("Replaying '{}' failed", proofFile, e);
            out.println("REPLAY incompatible " + errorMessage(e));
            return ExitCode.INPUT_ERROR.code();
        }
    }

    private int replay(PrintWriter out) throws Exception {
        Path file = proofFile;
        if (!Files.exists(file)) {
            out.println("REPLAY incompatible file not found: " + file);
            return ExitCode.INPUT_ERROR.code();
        }
        StatusMarker marker = StatusMarker.parse(readFirstLine(file));
        if (marker.malformed()) {
            out.println("REPLAY incompatible malformed status marker: '" + marker.line() + "'");
            return ExitCode.INPUT_ERROR.code();
        }
        try (var environment = KeYEnvironment.load(file)) {
            return replay(environment, marker);
        }
    }

    /**
     * Reads the first line of the given file (the status marker line, if any).
     *
     * @param file the proof file to inspect
     * @return the first line, or the empty string for an empty file
     * @throws IOException if the file cannot be read
     */
    private static String readFirstLine(Path file) throws IOException {
        try (var reader = Files.newBufferedReader(file)) {
            String firstLine = reader.readLine();
            return firstLine != null ? firstLine : "";
        }
    }

    private int replay(KeYEnvironment<?> environment, StatusMarker marker) {
        PrintWriter out = spec.commandLine().getOut();
        Proof proof = environment.getLoadedProof();
        if (proof == null) {
            out.println("REPLAY incompatible no proof found in file");
            return ExitCode.INPUT_ERROR.code();
        }
        String contractFilter = contract;
        if (contractFilter != null) {
            String obligationName = obligationName(environment, proof);
            if (!contractFilter.equals(obligationName)) {
                out.println("REPLAY incompatible proof obligation '" + obligationName + "' does "
                    + "not match --contract '" + contractFilter + "'");
                return ExitCode.INPUT_ERROR.code();
            }
        }
        ReplayResult replayResult = environment.getReplayResult();
        boolean replayFailed = replayResult == null || replayResult.hasErrors();
        if (marker.openGoals() != null) {
            // §7.2 G2: for header-carrying files the marker wins, even over a disagreeing
            // internal replay
            out.println("REPLAY unclosed " + marker.openGoals());
            return ExitCode.OPEN.code();
        }
        if (replayFailed) {
            out.println("REPLAY incompatible " + replayReason(replayResult));
            return ExitCode.INPUT_ERROR.code();
        }
        if (marker.closed()) {
            if (!proof.closed()) {
                out.println("REPLAY incompatible marker says closed but the proof has "
                    + proof.openGoals().size() + " open goal(s)");
                return ExitCode.INPUT_ERROR.code();
            }
            out.println("REPLAY closed 0");
            return ExitCode.CLOSED.code();
        }
        if (proof.closed()) {
            out.println("REPLAY closed 0");
            return ExitCode.CLOSED.code();
        }
        out.println("REPLAY unclosed " + proof.openGoals().size());
        return ExitCode.OPEN.code();
    }

    /**
     * Returns the canonical name of the obligation the given proof was loaded for, or
     * {@code null} if the proof has no obligation input.
     */
    private static @org.jspecify.annotations.Nullable String obligationName(
            KeYEnvironment<?> environment, Proof proof) {
        ProofOblInput po =
            environment.getServices().getSpecificationRepository().getProofOblInput(proof);
        if (po instanceof ContractPO contractPO) {
            return contractPO.getContract().getName();
        }
        return po == null ? null : po.name();
    }

    /**
     * Builds the human-readable reason for a failed internal replay.
     */
    private static String replayReason(@org.jspecify.annotations.Nullable ReplayResult result) {
        if (result == null) {
            return "no replay information for the loaded proof";
        }
        List<Throwable> errors = result.getErrorList();
        if (errors != null && !errors.isEmpty()) {
            Throwable first = errors.get(0);
            return oneLine("proof replay failed: "
                + (first.getMessage() != null ? first.getMessage()
                        : first.getClass()
                                .getSimpleName()));
        }
        return "proof replay failed";
    }

    private static String errorMessage(Exception e) {
        return oneLine(e.getMessage() != null ? e.getMessage() : e.getClass().getSimpleName());
    }

    /**
     * The protocol prints exactly one line, so any newlines in the reason are flattened.
     *
     * @param message the raw reason
     * @return the reason as a single line
     */
    private static String oneLine(String message) {
        return message.replaceAll("[\\r\\n]+", " ").trim();
    }

    /**
     * The first-line status marker of a proof file (§3 of the headless interface spec).
     *
     * @param line the raw first line of the file
     * @param closed the marker is {@code KEY_PROOF_STATUS closed 0}
     * @param openGoals the marker is {@code KEY_PROOF_STATUS open <n>}; {@code null} otherwise
     * @param malformed the first line starts with the marker prefix but is not a well-formed
     *        marker
     */
    record StatusMarker(String line, boolean closed,
            @org.jspecify.annotations.Nullable Integer openGoals, boolean malformed) {

        private static final String MARKER_PREFIX = ProofSaver.KEY_PROOF_STATUS_PREFIX + " ";

        /**
         * Interprets the given first line as a status marker.
         *
         * @param line the first line of the file
         * @return the parsed marker (never {@code null})
         */
        static StatusMarker parse(String line) {
            String l = line.endsWith("\r") ? line.substring(0, line.length() - 1) : line;
            if (!l.startsWith(MARKER_PREFIX)) {
                return new StatusMarker(line, false, null, false);
            }
            if (l.equals(ProofSaver.KEY_PROOF_STATUS_CLOSED)) {
                return new StatusMarker(line, true, null, false);
            }
            if (l.startsWith(ProofSaver.KEY_PROOF_STATUS_OPEN_PREFIX)) {
                String rest = l.substring(ProofSaver.KEY_PROOF_STATUS_OPEN_PREFIX.length());
                if (!rest.isEmpty() && rest.chars().allMatch(Character::isDigit)) {
                    return new StatusMarker(line, false, Integer.parseInt(rest), false);
                }
            }
            return new StatusMarker(line, false, null, true);
        }
    }
}
