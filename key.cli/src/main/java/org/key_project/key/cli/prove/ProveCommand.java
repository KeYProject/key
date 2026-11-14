/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.Callable;

import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import org.key_project.key.cli.CliError;
import org.key_project.key.cli.ContractResult;
import org.key_project.key.cli.ExitCode;
import org.key_project.key.cli.ResultRecordWriter;
import org.key_project.key.cli.ResultStatus;
import org.key_project.key.cli.settings.CliSettingsException;
import org.key_project.key.cli.settings.HeadlessRunnerSettings;

import picocli.CommandLine.Command;
import picocli.CommandLine.Model.CommandSpec;
import picocli.CommandLine.Option;
import picocli.CommandLine.Parameters;
import picocli.CommandLine.Spec;

/**
 * The {@code prove} subcommand: loads one or more KeY problem files, proves the selected
 * contracts, and prints one {@code KEY_RESULT} line per contract as the last lines of stdout.
 * The process exit code reflects the worst contract status.
 * <p>
 * Contracts are selected by repeated {@code --choose-contract} selectors (a bare index,
 * {@code NAME.#<IDX>}, or an exact canonical name, §4.2); without selectors the load file's
 * {@code \chooseContract}/{@code \proofObligation} directive selects the contract, and without
 * a directive all contracts are proven.
 * <p>
 * Strategy choices are layered per §5.1: repeated {@code --strategy-option <KEY>=<VALUE>} entries
 * override {@code --settings-file} entries for the same key, and both are applied only for the
 * duration of the run (never persisted back into {@code ~/.key}). An unknown key or undocumented
 * value is an input error ({@code KEY_ERROR settings: '...' not understood}, exit {@code 3}).
 * <p>
 * Proof-file honesty (§3): a proof file is written only where the caller requested one —
 * {@code --proof <PATH>} for single-contract runs, or {@code --proof-dir
 *
<DIR>
 * } for runs with
 * several contracts (files {@code <position>.proof}, 0-based selection position). A closed proof
 * is always written (first line {@code KEY_PROOF_STATUS closed 0}); an unclosed proof is written
 * only with {@code --save-partial} (first line {@code KEY_PROOF_STATUS open <n>}); without
 * {@code --proof}/{@code --proof-dir} nothing is written. {@code --proof} with several selected
 * contracts is an input error (exit {@code 3}). The written file is reported in each result's
 * {@code proofFile} field (absolute path or {@code null}).
 * <p>
 * Errors follow §1 of the headless interface spec and are reported as {@link CliError}s: input
 * errors (negative timeout, missing file, unknown contract, unloadable file) exit {@code 3}, and
 * unexpected exceptions while processing a file exit {@code 4}. A file that exists but cannot be
 * loaded additionally produces one error record (with the file name as its {@code contract} and a
 * non-{@code null} {@code errorMessage}) before the {@code KEY_ERROR} line is printed.
 */
@Command(name = "prove", description = "Prove the contracts of the given KeY problem file(s).",
    mixinStandardHelpOptions = true)
public final class ProveCommand implements Callable<Integer> {

    private final ResultRecordWriter resultWriter = new ResultRecordWriter();

    @Spec
    @SuppressWarnings("initialization.field.uninitialized")
    private CommandSpec spec;

    @Parameters(arity = "1..*", paramLabel = "<files>",
        description = "KeY problem files (.key) or Java sources whose contracts are proven.")
    private List<Path> files = List.of();

    @Option(names = "--timeout", paramLabel = "<MS>", defaultValue = "0",
        description = "Per-contract proof search timeout in milliseconds (0 = no timeout). "
            + "A search abandoned by the timeout is reported with status \"timed_out\" "
            + "and exit code 2.")
    private long timeout;

    @Option(names = "--choose-contract", paramLabel = "<SELECTOR>",
        description = "Select the contract(s) to prove, repeatable. A selector is a bare index "
            + "(the ordinal printed by `list`), NAME.#<IDX>, or an exact canonical contract "
            + "name (all contracts sharing the name are selected). Selection order is the "
            + "command-line order. Without this option the \\chooseContract/\\proofObligation "
            + "directive of the load file selects the contract, if present.")
    private List<String> chooseContract = List.of();

    @Option(names = "--settings-file", paramLabel = "<PATH>",
        description = "A §5.2 settings file (flat JSON) whose strategy choices are applied for "
            + "the run, with --strategy-option taking precedence per key.")
    @org.jspecify.annotations.Nullable
    private Path settingsFile;

    @Option(names = "--strategy-option", paramLabel = "<KEY>=<VALUE>",
        description = "Set a single strategy choice (§5.2 vocabulary), repeatable. An option "
            + "overrides --settings-file for its key, which overrides the load-file \\settings "
            + "and KeY defaults.")
    private List<String> strategyOption = List.of();

    @Option(names = "--proof", paramLabel = "<PATH>",
        description = "Write the saved proof of a single-contract run to this path (§3). The "
            + "file is written for a closed proof, and for an unclosed proof only with "
            + "--save-partial. Use --proof-dir for runs with several contracts.")
    @org.jspecify.annotations.Nullable
    private Path proof;

    @Option(names = "--proof-dir", paramLabel = "<DIR>",
        description = "Write the saved proofs of a multi-contract run into this directory as "
            + "<position>.proof files, one per selected contract in selection order (§3).")
    @org.jspecify.annotations.Nullable
    private Path proofDir;

    @Option(names = "--save-partial",
        description = "Also write the proof file of an unclosed proof (marked "
            + "'KEY_PROOF_STATUS open <n>') when --proof or --proof-dir is given (§3).")
    private boolean savePartial;

    /**
     * Runs the prove command.
     *
     * @return the exit code, {@code 0} if all contracts closed, otherwise the worst status code
     * @throws CliError an input error (negative timeout, missing file, unknown contract,
     *         unloadable file, conflicting {@code --proof}/{@code --proof-dir} usage) or an
     *         internal error; reported by the root command line as a {@code KEY_ERROR} line with
     *         the corresponding exit code (§1)
     */
    @Override
    public Integer call() throws CliError {
        if (timeout < 0) {
            throw CliError.input("--timeout must not be negative: " + timeout);
        }
        if (settingsFile != null && !Files.exists(settingsFile)) {
            throw CliError.input("file not found: " + settingsFile);
        }
        if (proof != null && proofDir != null) {
            throw CliError.input("--proof and --proof-dir are mutually exclusive");
        }
        for (Path file : files) {
            if (!Files.exists(file)) {
                throw CliError.input("file not found: " + file);
            }
        }

        HeadlessRunnerSettings runnerSettings;
        try {
            runnerSettings = HeadlessRunnerSettings.from(settingsFile, strategyOption);
        } catch (CliSettingsException e) {
            String message = e.getMessage();
            throw CliError.input(message != null ? message : e.getClass().getSimpleName());
        }

        PrintWriter out = spec.commandLine().getOut();
        HeadlessProver prover = new HeadlessProver(timeout, runnerSettings);
        ProofOutput output = new ProofOutput(proof, proofDir, savePartial);
        List<ContractResult> results = new ArrayList<>();
        for (Path file : files) {
            try {
                results.addAll(prover.prove(file, chooseContract, output));
            } catch (UnknownContractException e) {
                for (ContractIndex.Row row : e.index().list()) {
                    out.println(ContractIndex.renderLine(row));
                }
                out.flush();
                throw CliError.input("contract '" + e.selector() + "' not found");
            } catch (ProofOutputConflictException e) {
                throw CliError.input(errorMessage(e));
            } catch (ProblemLoaderException e) {
                ContractResult failure = loadFailureResult(file, e);
                out.println(resultWriter.toJsonLine(failure));
                out.flush();
                throw CliError.loadFailure(file, e);
            } catch (RuntimeException e) {
                throw CliError.internal("internal error while processing '" + file + "': "
                    + errorMessage(e), e);
            }
        }

        for (ContractResult result : results) {
            out.println(resultWriter.toJsonLine(result));
        }
        return ExitCode.worstOf(results).code();
    }

    /**
     * Creates the error record reported for a file that could not be loaded: the record's
     * {@code contract} field names the failed input file, and its {@code errorMessage} carries
     * the loader's failure message.
     *
     * @param file the file that could not be loaded
     * @param failure the loader exception
     * @return the error record for the failed file
     */
    private static ContractResult loadFailureResult(Path file, ProblemLoaderException failure) {
        String message = failure.getMessage() != null ? failure.getMessage()
                : failure.getClass().getSimpleName();
        return new ContractResult(file.toString(), ResultStatus.ERROR, 0, 0, null, 0, 0, message);
    }

    private static String errorMessage(Exception e) {
        return e.getMessage() != null ? e.getMessage() : e.getClass().getSimpleName();
    }
}
