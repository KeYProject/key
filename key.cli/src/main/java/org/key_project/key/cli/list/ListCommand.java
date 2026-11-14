/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.list;

import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.concurrent.Callable;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import org.key_project.key.cli.CliError;
import org.key_project.key.cli.ExitCode;
import org.key_project.key.cli.prove.ContractIndex;

import picocli.CommandLine.Command;
import picocli.CommandLine.Model.CommandSpec;
import picocli.CommandLine.Parameters;
import picocli.CommandLine.Spec;

/**
 * The {@code list} subcommand (§4.3 of the headless interface spec): loads the given KeY problem
 * files and prints one line per contract, {@code <IDX>\t<target>\t<NAME>}, in the stable index
 * order. The subcommand always exits {@code 0} on success and never prints a {@code KEY_RESULT}
 * line. Errors are reported as {@link CliError}s (missing or unloadable file: input error, exit
 * {@code 3}; unexpected exception: internal error, exit {@code 4}).
 */
@Command(name = "list",
    description = "List the contracts of the given KeY problem file(s), one tab-separated line "
        + "'<IDX>\t<target>\t<NAME>' per contract in stable order.",
    mixinStandardHelpOptions = true)
public final class ListCommand implements Callable<Integer> {

    @Spec
    @SuppressWarnings("initialization.field.uninitialized")
    private CommandSpec spec;

    @Parameters(arity = "1..*", paramLabel = "<files>",
        description = "KeY problem files (.key) or Java sources whose contracts are listed.")
    private List<Path> files = List.of();

    /**
     * Lists the contracts of the given files.
     *
     * @return the exit code, {@code 0} on success
     * @throws CliError an input error (missing file, unloadable file) or an internal error;
     *         reported by the root command line as a {@code KEY_ERROR} line with the
     *         corresponding exit code ({@code 3} or {@code 4}, §1)
     */
    @Override
    public Integer call() throws CliError {
        PrintWriter out = spec.commandLine().getOut();

        for (Path file : files) {
            if (!Files.exists(file)) {
                throw CliError.input("file not found: " + file);
            }
            try {
                KeYEnvironment<?> environment = KeYEnvironment.load(file);
                try {
                    for (ContractIndex.Row row : ContractIndex.fromEnvironment(environment)
                            .list()) {
                        out.println(ContractIndex.renderLine(row));
                    }
                } finally {
                    environment.dispose();
                }
            } catch (ProblemLoaderException e) {
                throw CliError.loadFailure(file, e);
            } catch (RuntimeException e) {
                throw CliError.internal("internal error while listing '" + file + "': "
                    + errorMessage(e), e);
            }
        }
        return ExitCode.CLOSED.code();
    }

    private static String errorMessage(Exception e) {
        return e.getMessage() != null ? e.getMessage() : e.getClass().getSimpleName();
    }
}
