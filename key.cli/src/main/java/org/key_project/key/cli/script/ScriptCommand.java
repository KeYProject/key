/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.script;

import java.io.IOException;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.concurrent.Callable;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.Contract;

import org.key_project.key.cli.CliError;
import org.key_project.key.cli.ContractResult;
import org.key_project.key.cli.ResultRecordWriter;
import org.key_project.key.cli.prove.ContractIndex;
import org.key_project.key.cli.prove.ContractSelector;
import org.key_project.key.cli.prove.HeadlessProver;
import org.key_project.key.cli.prove.ObligationCreationException;
import org.key_project.key.cli.prove.SmtCounters;
import org.key_project.key.cli.prove.UnknownContractException;
import org.key_project.key.cli.settings.CliSettingsException;
import org.key_project.key.cli.settings.HeadlessRunnerSettings;

import org.jspecify.annotations.Nullable;
import picocli.CommandLine.Command;
import picocli.CommandLine.Model.CommandSpec;
import picocli.CommandLine.Option;
import picocli.CommandLine.Parameters;
import picocli.CommandLine.Spec;

/**
 * The {@code script} subcommand (§7.1 of the headless interface spec): executes a line-oriented
 * proof script against one obligation of a KeY problem file.
 * <p>
 * The script file is read as UTF-8; every line is one of {@code proceed},
 * {@code apply <rule-name> [at <position-path>] [for <term>]}, {@code auto [<limit>]},
 * {@code assert-closed} or {@code print-open-goals}. Empty lines and lines starting with
 * {@code #} are ignored. Each executed line is acknowledged as {@code SCRIPT OK <line>} or
 * {@code SCRIPT FAIL <line> <reason>}, the second-to-last line of stdout is
 * {@code SCRIPT FINAL closed} or {@code SCRIPT FINAL open <n>}, and the last line is exactly one
 * §2 {@code KEY_RESULT} record carrying the outcome of the run (exit {@code 0} closed, {@code 1}
 * open, {@code 2} timed out).
 * <p>
 * The obligation is chosen by §4: repeated {@code --choose-contract} selectors, otherwise the load
 * file's {@code \chooseContract}/{@code \proofObligation} directive, otherwise all contracts of
 * the problem. A script can only be applied to a single obligation, so a selection that does not
 * resolve to exactly one contract is an input error (exit {@code 3}).
 * <p>
 * A load file that exists but cannot be loaded, or a selected obligation whose proof cannot be
 * created ({@link org.key_project.key.cli.prove.ObligationCreationException}), is an input error
 * (exit {@code 3}) reported the same way as by {@code prove}: one {@code "status":"error"} record
 * (with the file name or the contract name as its {@code contract} and a non-{@code null}
 * {@code errorMessage}) as the last stdout line, then the {@code KEY_ERROR} line on stderr.
 * <p>
 * {@code --timeout <MS>} bounds each strategy command ({@code proceed}/{@code auto}) of the
 * script.
 * <p>
 * Strategy choices are layered per §5.1 exactly as in {@code prove}: repeated
 * {@code --strategy-option <KEY>=<VALUE>} entries override {@code --settings-file} entries for the
 * same key, and both are applied only for the duration of the run. An unknown key or undocumented
 * value is an input error (exit {@code 3}). {@code --config-dir} is handled by
 * {@link org.key_project.key.cli.Main}'s pre-scan.
 */
@Command(name = "script",
    description = "Execute a §7.1 proof script against one obligation of a KeY problem file.",
    mixinStandardHelpOptions = true)
public final class ScriptCommand implements Callable<Integer> {

    @Spec
    @SuppressWarnings("initialization.field.uninitialized")
    private CommandSpec spec;

    @Parameters(index = "0", paramLabel = "<load-file>",
        description = "The KeY problem file (.key) or Java source to load.")
    @SuppressWarnings("initialization.field.uninitialized")
    private Path loadFile;

    @Parameters(index = "1", paramLabel = "<script-file>",
        description = "The line-oriented §7.1 script file to execute (UTF-8).")
    @SuppressWarnings("initialization.field.uninitialized")
    private Path scriptFile;

    @Option(names = "--timeout", paramLabel = "<MS>", defaultValue = "0",
        description = "Per-command proof-search timeout in milliseconds (0 = no timeout). "
            + "A command cut short by the timeout fails and the run exits 2.")
    private long timeout;

    @Option(names = "--choose-contract", paramLabel = "<SELECTOR>",
        description = "Select the obligation to run the script against, repeatable and with the "
            + "same selector syntax as `prove`. The selection must resolve to exactly one "
            + "contract.")
    private List<String> chooseContract = List.of();

    @Option(names = "--settings-file", paramLabel = "<PATH>",
        description = "A §5.2 settings file (flat JSON) whose strategy choices are applied for "
            + "the run, with --strategy-option taking precedence per key.")
    @Nullable
    private Path settingsFile;

    @Option(names = "--strategy-option", paramLabel = "<KEY>=<VALUE>",
        description = "Set a single strategy choice (§5.2 vocabulary), repeatable. An option "
            + "overrides --settings-file for its key, which overrides the load-file \\settings "
            + "and KeY defaults.")
    private List<String> strategyOption = List.of();

    private final ResultRecordWriter resultWriter = new ResultRecordWriter();

    /**
     * Loads the problem, selects the obligation, executes the script, prints the §2 result
     * record and returns the exit code.
     *
     * @return the §1 exit code: {@code 0} if the proof is closed at the end of the script,
     *         {@code 2} if the proof search was abandoned because of the timeout, {@code 1} if
     *         goals remain open
     * @throws CliError an input error (negative timeout, missing file, unknown or ambiguous
     *         contract, unreadable script, unloadable problem) or an internal error (§1)
     */
    @Override
    public Integer call() throws CliError {
        if (timeout < 0) {
            throw CliError.input("--timeout must not be negative: " + timeout);
        }
        requireFile(loadFile);
        requireFile(scriptFile);
        List<String> lines = readScript();
        HeadlessRunnerSettings runnerSettings = runnerSettings();

        PrintWriter out = spec.commandLine().getOut();
        runnerSettings.apply();
        try {
            KeYEnvironment<DefaultUserInterfaceControl> environment = KeYEnvironment.load(loadFile);
            try {
                validateSettings(runnerSettings);
                Contract contract = selectSingleObligation(environment);
                Proof proof = HeadlessProver.createProof(environment, contract);
                try {
                    ScriptInterpreter interpreter =
                        new ScriptInterpreter(contract, proof, environment.getUi(), timeout, out);
                    int exit = interpreter.execute(lines);
                    printResult(out, contract, proof, interpreter);
                    return exit;
                } finally {
                    if (!proof.isDisposed()) {
                        proof.dispose();
                    }
                }
            } finally {
                environment.dispose();
            }
        } catch (UnknownContractException e) {
            throw CliError.input(errorMessage(e));
        } catch (ObligationCreationException e) {
            // input error (§1 exit 3): the failed obligation is reported as an error record
            out.println(resultWriter.toJsonLine(e.record()));
            out.flush();
            throw e.cliError();
        } catch (ProblemLoaderException e) {
            out.println(resultWriter.toJsonLine(CliError.loadFailureRecord(loadFile, e)));
            out.flush();
            throw CliError.loadFailure(loadFile, e);
        } catch (CliError e) {
            throw e;
        } catch (RuntimeException e) {
            throw CliError.internal("internal error while running the script: "
                + errorMessage(e), e);
        } finally {
            runnerSettings.close();
        }
    }

    /**
     * Assembles the §5.1 strategy settings of the run from {@code --settings-file} and
     * {@code --strategy-option}.
     *
     * @return the run settings, never {@code null} (empty if no option was given)
     * @throws CliError an input error if the settings file cannot be read or an option is not
     *         understood
     */
    private HeadlessRunnerSettings runnerSettings() throws CliError {
        try {
            return HeadlessRunnerSettings.from(settingsFile, strategyOption);
        } catch (CliSettingsException e) {
            String message = e.getMessage();
            throw CliError.input(message != null ? message : e.getClass().getSimpleName());
        }
    }

    /**
     * Verifies the requested strategy choices against the choice declarations of the loaded
     * problem (§5.3 of the headless interface spec).
     *
     * @param settings the run settings
     * @throws CliError an input error naming the offending {@code category:value}
     */
    private static void validateSettings(HeadlessRunnerSettings settings) throws CliError {
        try {
            settings.validate();
        } catch (CliSettingsException e) {
            String message = e.getMessage();
            throw CliError.input(message != null ? message : e.getClass().getSimpleName());
        }
    }

    /**
     * Prints the §2 {@code KEY_RESULT} record of the run as the last stdout line. The record is
     * built while the proof is still alive, because the open-goal count and the SMT counters read
     * the proof tree.
     *
     * @param out the writer that receives the record
     * @param contract the obligation the script ran against
     * @param proof the finished proof, not yet disposed
     * @param interpreter the interpreter that executed the script
     */
    private void printResult(PrintWriter out, Contract contract, Proof proof,
            ScriptInterpreter interpreter) {
        SmtCounters.Counts smt = SmtCounters.of(proof);
        ContractResult result = new ContractResult(contract.getName(), interpreter.status(),
            proof.openGoals().size(), interpreter.elapsedMs(), null, smt.smtCalls(),
            smt.smtProved(), null);
        out.println(resultWriter.toJsonLine(result));
        out.flush();
    }

    private static void requireFile(Path file) throws CliError {
        if (!Files.exists(file)) {
            throw CliError.input("file not found: " + file);
        }
    }

    private List<String> readScript() throws CliError {
        try {
            return Files.readAllLines(scriptFile, StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw CliError.input("cannot read script '" + scriptFile + "': " + errorMessage(e));
        }
    }

    /**
     * Loads a problem and resolves the §4 selection to the single obligation a script can run
     * against.
     *
     * @param environment the loaded environment
     * @return the selected obligation
     * @throws UnknownContractException if a selector matches no contract
     * @throws CliError if the selection does not resolve to exactly one contract
     */
    private Contract selectSingleObligation(KeYEnvironment<?> environment)
            throws UnknownContractException {
        ContractIndex index = ContractIndex.fromEnvironment(environment);
        List<Contract> selected = chooseContract.isEmpty()
                ? defaultSelection(environment, index)
                : ContractSelector.resolve(index, chooseContract);
        if (selected.size() != 1) {
            throw CliError.input("script requires exactly one selected obligation, but "
                + selected.size() + " were selected (use --choose-contract)");
        }
        return selected.get(0);
    }

    /**
     * Returns the contracts selected by the load file's {@code \chooseContract}/
     * {@code \proofObligation} directive, or all contracts of the problem if it selects none.
     */
    private static List<Contract> defaultSelection(KeYEnvironment<?> environment,
            ContractIndex index) {
        Contract loadFileContract = loadFileContract(environment);
        return loadFileContract != null ? List.of(loadFileContract) : index.contracts();
    }

    private static @Nullable Contract loadFileContract(KeYEnvironment<?> environment) {
        Proof loaded = environment.getLoadedProof();
        if (loaded == null) {
            return null;
        }
        ProofOblInput po =
            environment.getServices().getSpecificationRepository().getProofOblInput(loaded);
        return po instanceof ContractPO contractPO ? contractPO.getContract() : null;
    }

    private static String errorMessage(Exception e) {
        return e.getMessage() != null ? e.getMessage() : e.getClass().getSimpleName();
    }
}
