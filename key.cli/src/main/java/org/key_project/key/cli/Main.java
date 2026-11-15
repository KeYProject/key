/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli;

import java.io.PrintWriter;
import java.util.concurrent.Callable;

import de.uka.ilkd.key.settings.PathConfig;

import org.key_project.key.cli.list.ListCommand;
import org.key_project.key.cli.prove.ProveCommand;
import org.key_project.key.cli.replay.ReplayCommand;
import org.key_project.key.cli.script.ScriptCommand;

import picocli.CommandLine;
import picocli.CommandLine.Command;
import picocli.CommandLine.IParameterExceptionHandler;
import picocli.CommandLine.Model.CommandSpec;
import picocli.CommandLine.Option;
import picocli.CommandLine.ParseResult;
import picocli.CommandLine.ScopeType;
import picocli.CommandLine.Spec;

/**
 * Entry point of the headless KeY command-line interface.
 * <p>
 * This class is the picocli root command. Before the command line is parsed, {@link #main}
 * pre-scans the arguments for a {@code --config-dir} option and redirects KeY's user-persistence
 * directory (the {@code key.home} system property) accordingly, so that KeY never touches
 * {@code ~/.key} when requested otherwise. The pre-scan runs before any KeY class is loaded.
 */
@Command(name = "key-cli",
    description = "Headless command-line interface for KeY.",
    mixinStandardHelpOptions = true,
    subcommands = { ProveCommand.class, ListCommand.class, ReplayCommand.class,
        ScriptCommand.class })
public final class Main implements Callable<Integer> {

    @Spec
    @SuppressWarnings("initialization.field.uninitialized")
    private CommandSpec spec;

    @Option(names = "--config-dir", paramLabel = "<DIR>", scope = ScopeType.INHERIT,
        description = "Use DIR as the base directory for all of KeY's user-persistence "
            + "(default: ~/.key).")
    @org.jspecify.annotations.Nullable
    private String configDir;

    /**
     * Program entry point.
     *
     * @param args the command-line arguments
     */
    public static void main(String[] args) {
        System.exit(run(args));
    }

    /**
     * Runs the CLI with the given arguments and returns the process exit code.
     *
     * @param args the command-line arguments
     * @return the exit code as specified by the headless interface contract
     */
    public static int run(String[] args) {
        preScanConfigDir(args);
        Log.configureLogging(Verbosity.ERROR);
        return createCommandLine().execute(args);
    }

    /**
     * Creates the picocli command line for the root command with custom error handlers mapping
     * usage errors and unexpected exceptions to the documented exit codes.
     *
     * @return the configured {@link CommandLine}
     */
    public static CommandLine createCommandLine() {
        return new CommandLine(new Main())
                .setOut(new ProtocolWriter(System.out))
                .setErr(new ProtocolWriter(System.err))
                .setParameterExceptionHandler(new ParameterExceptionHandler())
                .setExecutionExceptionHandler(new ExecutionExceptionHandler());
    }

    /**
     * Invoked when the CLI is executed without a subcommand.
     *
     * @return the input-error exit code, since a subcommand is required
     */
    @Override
    public Integer call() {
        PrintWriter err = spec.commandLine().getErr();
        err.println("KEY_ERROR subcommand required (e.g. `prove`).");
        err.println(spec.commandLine().getUsageMessage());
        return ExitCode.INPUT_ERROR.code();
    }

    /**
     * Pre-scans the raw arguments for a {@code --config-dir} option and sets the
     * {@code key.home} system property before any KeY class is loaded. An explicit
     * {@code --config-dir} overrides a previously set {@code key.home} property
     * (e.g. via {@code -Dkey.home=...}).
     *
     * @param args the raw command-line arguments
     */
    static void preScanConfigDir(String[] args) {
        String dir = findConfigDir(args);
        if (dir != null && !dir.isEmpty()) {
            System.setProperty(PathConfig.KEY_HOME_PROPERTY, dir);
        }
    }

    private static @org.jspecify.annotations.Nullable String findConfigDir(String[] args) {
        for (int i = 0; i < args.length; i++) {
            String arg = args[i];
            if ("--config-dir".equals(arg) && i + 1 < args.length) {
                return args[i + 1];
            }
            String prefix = "--config-dir=";
            if (arg.startsWith(prefix)) {
                return arg.substring(prefix.length());
            }
        }
        return null;
    }

    /**
     * Remaps picocli usage errors (unknown options, missing arguments, ...) to the input-error
     * exit code {@code 3}.
     */
    private static final class ParameterExceptionHandler implements IParameterExceptionHandler {
        @Override
        public int handleParseException(CommandLine.ParameterException ex, String[] args) {
            CommandLine commandLine = ex.getCommandLine();
            PrintWriter err = commandLine.getErr();
            err.println("KEY_ERROR " + ex.getMessage());
            err.println(commandLine.getUsageMessage());
            return ExitCode.INPUT_ERROR.code();
        }
    }

    /**
     * Remaps unexpected execution exceptions to a {@code KEY_ERROR} line and the exit code of the
     * exception: {@link CliError}s exit with their kind's code, everything else as an internal
     * error.
     */
    private static final class ExecutionExceptionHandler
            implements CommandLine.IExecutionExceptionHandler {
        @Override
        public int handleExecutionException(Exception ex, CommandLine commandLine,
                ParseResult parseResult) {
            return Main.handleExecutionException(ex, commandLine.getErr());
        }
    }

    /**
     * Prints a {@code KEY_ERROR} line for the given execution-time exception and returns the
     * process exit code (§1): a {@link CliError} is reported with the message and the exit code
     * of its kind ({@code 3} for input errors, {@code 4} for internal errors); any other
     * exception is an internal error with exit code {@code 4}. The message is flattened to a
     * single line because consumers read the protocol line by line (§2).
     *
     * @param ex the exception thrown by the invoked command
     * @param err the writer the {@code KEY_ERROR} line is printed to (stderr)
     * @return the process exit code
     */
    static int handleExecutionException(Exception ex, PrintWriter err) {
        if (ex instanceof CliError cliError) {
            err.println("KEY_ERROR " + CliError.oneLine(cliError.getMessage()));
            return cliError.kind().exitCode().code();
        }
        String message =
            ex.getMessage() != null ? ex.getMessage() : ex.getClass().getSimpleName();
        err.println("KEY_ERROR internal error: " + CliError.oneLine(message));
        return ExitCode.INTERNAL_ERROR.code();
    }
}
