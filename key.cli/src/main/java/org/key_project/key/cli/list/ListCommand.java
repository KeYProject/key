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
 * line.
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
     * @return the exit code, {@code 0} on success, {@code 3} on input errors, {@code 4} on
     *         internal errors
     */
    @Override
    public Integer call() {
        PrintWriter out = spec.commandLine().getOut();
        PrintWriter err = spec.commandLine().getErr();

        for (Path file : files) {
            if (!Files.exists(file)) {
                err.println("KEY_ERROR file not found: " + file);
                return ExitCode.INPUT_ERROR.code();
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
                err.println("KEY_ERROR cannot load '" + file + "': " + e.getMessage());
                return ExitCode.INPUT_ERROR.code();
            } catch (RuntimeException e) {
                err.println("KEY_ERROR internal error while loading '" + file + "': "
                    + errorMessage(e));
                return ExitCode.INTERNAL_ERROR.code();
            }
        }
        return ExitCode.CLOSED.code();
    }

    private static String errorMessage(Exception e) {
        return e.getMessage() != null ? e.getMessage() : e.getClass().getSimpleName();
    }
}
