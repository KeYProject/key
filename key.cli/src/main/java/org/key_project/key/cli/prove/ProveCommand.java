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

import org.key_project.key.cli.ContractResult;
import org.key_project.key.cli.ExitCode;
import org.key_project.key.cli.ResultRecordWriter;

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
            + "Note: the timed_out result status is not yet determined in this phase.")
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
     */
    @Override
    public Integer call() {
        PrintWriter out = spec.commandLine().getOut();
        PrintWriter err = spec.commandLine().getErr();

        if (timeout < 0) {
            err.println("KEY_ERROR --timeout must not be negative: " + timeout);
            return ExitCode.INPUT_ERROR.code();
        }
        for (Path file : files) {
            if (!Files.exists(file)) {
                err.println("KEY_ERROR file not found: " + file);
                return ExitCode.INPUT_ERROR.code();
            }
        }

        HeadlessProver prover = new HeadlessProver(timeout);
        List<ContractResult> results = new ArrayList<>();
        for (Path file : files) {
            try {
                results.addAll(prover.prove(file, chooseContract));
            } catch (UnknownContractException e) {
                for (ContractIndex.Row row : e.index().list()) {
                    out.println(ContractIndex.renderLine(row));
                }
                err.println("KEY_ERROR contract '" + e.selector() + "' not found");
                return ExitCode.INPUT_ERROR.code();
            } catch (ProblemLoaderException e) {
                err.println("KEY_ERROR cannot load '" + file + "': " + e.getMessage());
                return ExitCode.INPUT_ERROR.code();
            } catch (RuntimeException e) {
                err.println("KEY_ERROR internal error while loading '" + file + "': "
                    + errorMessage(e));
                return ExitCode.INTERNAL_ERROR.code();
            }
        }

        for (ContractResult result : results) {
            out.println(resultWriter.toJsonLine(result));
        }
        return ExitCode.worstOf(results).code();
    }

    private static String errorMessage(Exception e) {
        return e.getMessage() != null ? e.getMessage() : e.getClass().getSimpleName();
    }
}
