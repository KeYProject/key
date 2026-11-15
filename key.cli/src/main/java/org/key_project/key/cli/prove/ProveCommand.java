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
import java.util.Map;
import java.util.Stack;
import java.util.concurrent.Callable;
import java.util.regex.Pattern;

import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import org.key_project.key.cli.CliError;
import org.key_project.key.cli.ContractResult;
import org.key_project.key.cli.ExitCode;
import org.key_project.key.cli.ResultRecordWriter;
import org.key_project.key.cli.settings.CliSettingsException;
import org.key_project.key.cli.settings.HeadlessRunnerSettings;

import picocli.CommandLine.Command;
import picocli.CommandLine.IParameterConsumer;
import picocli.CommandLine.IParameterPreprocessor;
import picocli.CommandLine.Model.ArgSpec;
import picocli.CommandLine.Model.CommandSpec;
import picocli.CommandLine.Model.OptionSpec;
import picocli.CommandLine.Option;
import picocli.CommandLine.ParameterException;
import picocli.CommandLine.Parameters;
import picocli.CommandLine.Spec;

/**
 * The {@code prove} subcommand: loads one or more KeY problem files, proves the selected
 * contracts, and prints one {@code KEY_RESULT} line per contract. Each file's records are
 * printed as soon as that file's contracts have finished, in file order and, within a file,
 * selection order, so a run aborted by a later file leaves the completed files' records on
 * stdout; for a completed run the records are the last lines of stdout. The process exit code
 * reflects the worst contract status.
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
 * {@code --proof}/{@code --proof-dir} nothing is written. Proof output requires exactly one load
 * file: {@code --proof} with several selected contracts, and {@code --proof} or
 * {@code --proof-dir} with several load files, are input errors (exit {@code 3}) because the
 * outputs would otherwise overwrite each other (the {@code --proof-dir} file numbering is per
 * run). A requested proof file that cannot be written is an input error as well, never a silent
 * success. The written file is reported in each result's {@code proofFile} field (absolute path
 * or {@code null}).
 * <p>
 * With {@code --print-open-goals [MAX]} (§6), the open goals of each contract are printed after
 * proof search and before the {@code KEY_RESULT} lines, one section per contract in selection
 * order: a {@code CONTRACT <NAME>} label line, an {@code OPEN-GOAL-COUNT} line with the true
 * total, followed by up to {@code MAX} {@code GOAL} blocks (default {@code 10},
 * {@code 0} = unlimited); {@code --no-truncate-formulas} disables the length truncation of
 * printed formulas. {@code MAX} is optional and bound only to a following integer literal, so
 * {@code --print-open-goals spec.key} keeps {@code spec.key} as a load file; the attached form
 * {@code --print-open-goals=<MAX>} is also accepted and must be an integer.
 * <p>
 * Errors follow §1 of the headless interface spec and are reported as {@link CliError}s: input
 * errors (negative timeout, missing file, unknown contract, unloadable file, an obligation that
 * cannot be created, no contracts found, unwritable proof file) exit {@code 3}, and unexpected
 * exceptions while processing a file exit {@code 4}. A file that exists but cannot be loaded — or
 * a contract whose proof obligation cannot be created — additionally produces one error record
 * (with the file name or the contract name as its {@code contract} and a non-{@code null}
 * {@code errorMessage}) before the {@code KEY_ERROR} line is printed, and the run aborts: the
 * remaining contracts are not proven. A run that selects no contract at all is an input error,
 * since §1 reserves exit {@code 0} for a run with at least one contract, all closed.
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
            + "--save-partial. Requires exactly one load file; use --proof-dir for runs with "
            + "several contracts.")
    @org.jspecify.annotations.Nullable
    private Path proof;

    @Option(names = "--proof-dir", paramLabel = "<DIR>",
        description = "Write the saved proofs of a multi-contract run into this directory as "
            + "<position>.proof files, one per selected contract in selection order (§3). "
            + "Requires exactly one load file; the numbering is per run, so prove one file per "
            + "invocation.")
    @org.jspecify.annotations.Nullable
    private Path proofDir;

    @Option(names = "--save-partial",
        description = "Also write the proof file of an unclosed proof (marked "
            + "'KEY_PROOF_STATUS open <n>') when --proof or --proof-dir is given (§3).")
    private boolean savePartial;

    @Option(names = "--print-open-goals", arity = "0..1", fallbackValue = "10",
        paramLabel = "[<MAX>]", parameterConsumer = OpenGoalsParameterHandler.class,
        preprocessor = OpenGoalsParameterHandler.class,
        description = "After proof search, print the open goals to stdout: one section per "
            + "selected contract, each starting with a CONTRACT <name> label line, then an "
            + "OPEN-GOAL-COUNT line (always the true total) followed by up to MAX GOAL blocks "
            + "with their position paths (0 = unlimited, default 10). The value is optional: a "
            + "following integer is taken as MAX, so `--print-open-goals spec.key` treats "
            + "spec.key as a load file.")
    private @org.jspecify.annotations.Nullable Integer printOpenGoals;

    @Option(names = "--no-truncate-formulas",
        description = "Disable the length truncation of formulas in the --print-open-goals "
            + "output.")
    private boolean noTruncateFormulas;

    /**
     * Runs the prove command.
     *
     * @return the exit code, {@code 0} if all contracts closed, otherwise the worst status code
     * @throws CliError an input error (negative timeout, missing file, unknown contract,
     *         unloadable file, no contracts found, conflicting {@code --proof}/{@code
     *         --proof-dir} usage, proof output with several load files, unwritable proof file) or
     *         an internal error; reported by the root command line as a {@code KEY_ERROR} line
     *         with the corresponding exit code (§1)
     */
    @Override
    public Integer call() throws CliError {
        if (timeout < 0) {
            throw CliError.input("--timeout must not be negative: " + timeout);
        }
        if (printOpenGoals != null && printOpenGoals < 0) {
            throw CliError.input("--print-open-goals must not be negative: " + printOpenGoals);
        }
        if (settingsFile != null && !Files.exists(settingsFile)) {
            throw CliError.input("file not found: " + settingsFile);
        }
        if (proof != null && proofDir != null) {
            throw CliError.input("--proof and --proof-dir are mutually exclusive");
        }
        if (files.size() > 1 && (proof != null || proofDir != null)) {
            throw CliError.input("proof output (--proof/--proof-dir) requires a single load "
                + "file, but " + files.size() + " were given; run prove once per file so the "
                + "proofs do not overwrite each other (the --proof-dir numbering is per run)");
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
        if (printOpenGoals != null) {
            prover.setOpenGoalPrinter(
                new OpenGoalPrinter(out, printOpenGoals, !noTruncateFormulas));
        }
        List<ContractResult> results = new ArrayList<>();
        for (Path file : files) {
            List<ContractResult> fileResults;
            try {
                fileResults = prover.prove(file, chooseContract, output);
            } catch (UnknownContractException e) {
                for (ContractIndex.Row row : e.index().list()) {
                    out.println(ContractIndex.renderLine(row));
                }
                out.flush();
                throw CliError.input("contract '" + e.selector() + "' not found");
            } catch (ProofOutputConflictException e) {
                throw CliError.input(CliError.errorMessage(e));
            } catch (ObligationCreationException e) {
                // input error (§1 exit 3): the failed contract is reported as an error record
                out.println(resultWriter.toJsonLine(e.record()));
                out.flush();
                throw e.cliError();
            } catch (ProblemLoaderException e) {
                out.println(resultWriter.toJsonLine(CliError.loadFailureRecord(file, e)));
                out.flush();
                throw CliError.loadFailure(file, e);
            } catch (CliError e) {
                // already a CLI-level error (e.g. an unwritable proof file): report it verbatim
                throw e;
            } catch (RuntimeException e) {
                throw CliError.internal("internal error while processing '" + file + "': "
                    + CliError.errorMessage(e), e);
            }
            results.addAll(fileResults);
            // stream this file's records as soon as it finished: if a later file fails, the
            // completed files' records are already on stdout (§2)
            for (ContractResult result : fileResults) {
                out.println(resultWriter.toJsonLine(result));
            }
        }
        if (results.isEmpty()) {
            // §1: exit 0 means "one or more contracts, all closed"
            throw CliError.input("no contracts found in " + fileList());
        }

        return ExitCode.worstOf(results).code();
    }

    /**
     * Renders the load files of this run for an error message.
     *
     * @return the file paths, separated by {@code ", "}
     */
    private String fileList() {
        return String.join(", ", files.stream().map(Path::toString).toList());
    }

    /**
     * Handling of the optional value of {@code --print-open-goals}: the following argument is
     * bound as the option's {@code MAX} value only if it is an integer literal ({@code -?\d+}).
     * Any other argument (notably a load file) is left on the stack, so
     * {@code --print-open-goals spec.key} keeps working as a bare flag with the fallback value
     * {@code 10}.
     * <p>
     * The parameter consumer binds the value; the preprocessor only rejects an explicitly
     * attached non-integer value such as {@code --print-open-goals=abc}, which picocli would
     * otherwise leave on the stack as if it were a load file.
     */
    static final class OpenGoalsParameterHandler
            implements IParameterConsumer, IParameterPreprocessor {

        private static final Pattern INTEGER_LITERAL = Pattern.compile("-?\\d+");

        /**
         * Rejects an attached value ({@code --print-open-goals=<value>}) that is not an integer
         * literal; every other case is left to the parameter consumer.
         *
         * @param args the arguments following the matched option
         * @param commandSpec the command the option belongs to
         * @param argSpec the matched option
         * @param info the parser state, including the separator used to attach the value
         * @return always {@code false}, so the parameter consumer binds the value
         */
        @Override
        public boolean preprocess(Stack<String> args, CommandSpec commandSpec, ArgSpec argSpec,
                Map<String, Object> info) {
            boolean attached = !" ".equals(String.valueOf(info.get("separator")));
            String next = args.isEmpty() ? null : args.peek();
            if (attached && next != null && !INTEGER_LITERAL.matcher(next).matches()) {
                throw invalidValue(commandSpec, next);
            }
            return false;
        }

        /**
         * Binds the following argument as {@code MAX} if it is an integer literal, and the
         * declared fallback value {@code 10} otherwise; the argument is only removed from the
         * stack when it is consumed.
         *
         * @param args the arguments following the matched option
         * @param argSpec the matched option
         * @param commandSpec the command the option belongs to
         */
        @Override
        public void consumeParameters(Stack<String> args, ArgSpec argSpec,
                CommandSpec commandSpec) {
            String next = args.isEmpty() ? null : args.peek();
            if (next == null || !INTEGER_LITERAL.matcher(next).matches()) {
                argSpec.setValue(fallbackMax(argSpec));
                return;
            }
            args.pop();
            try {
                argSpec.setValue(Integer.valueOf(next));
            } catch (NumberFormatException e) {
                throw invalidValue(commandSpec, next);
            }
        }

        /**
         * Creates the usage error reported for a {@code MAX} value that is not an integer.
         *
         * @param commandSpec the command the option belongs to
         * @param value the offending value
         * @return the usage error, reported as a {@code KEY_ERROR} line with exit code {@code 3}
         */
        private static ParameterException invalidValue(CommandSpec commandSpec, String value) {
            return new ParameterException(commandSpec.commandLine(),
                "Invalid value for option '--print-open-goals': '" + value
                    + "' is not an integer");
        }

        /**
         * Returns the option's declared fallback value, i.e. the {@code MAX} used when no
         * integer literal follows the option.
         *
         * @param argSpec the option being parsed
         * @return the fallback {@code MAX}
         */
        private static Integer fallbackMax(ArgSpec argSpec) {
            String fallback = argSpec.isOption() ? ((OptionSpec) argSpec).fallbackValue() : "";
            return Integer.valueOf(fallback.isEmpty() ? "10" : fallback);
        }
    }
}
