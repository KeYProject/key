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

    /**
     * Runs the prove command.
     *
     * @return the exit code, {@code 0} if all contracts closed, otherwise the worst status code
     * @throws CliError an input error (negative timeout, missing file, unknown contract,
     *         unloadable file) or an internal error; reported by the root command line as a
     *         {@code KEY_ERROR} line with the corresponding exit code (§1)
     */
    @Override
    public Integer call() throws CliError {
        if (timeout < 0) {
            throw CliError.input("--timeout must not be negative: " + timeout);
        }
        for (Path file : files) {
            if (!Files.exists(file)) {
                throw CliError.input("file not found: " + file);
            }
        }

        PrintWriter out = spec.commandLine().getOut();
        HeadlessProver prover = new HeadlessProver(timeout);
        List<ContractResult> results = new ArrayList<>();
        for (Path file : files) {
            try {
                results.addAll(prover.prove(file, chooseContract));
            } catch (UnknownContractException e) {
                for (ContractIndex.Row row : e.index().list()) {
                    out.println(ContractIndex.renderLine(row));
                }
                out.flush();
                throw CliError.input("contract '" + e.selector() + "' not found");
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
