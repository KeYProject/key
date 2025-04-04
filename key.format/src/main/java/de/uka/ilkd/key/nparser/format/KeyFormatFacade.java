/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.format;/*
                                        * This file is part of KeY - https://key-project.org
                                        * KeY is licensed under the GNU General Public License
                                        * Version 2
                                        * SPDX-License-Identifier: GPL-2.0-only
                                        */

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.Callable;

import de.uka.ilkd.key.util.parsing.SyntaxErrorReporter;

import org.antlr.v4.runtime.CharStreams;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import picocli.CommandLine;
import picocli.CommandLine.Command;
import picocli.CommandLine.Parameters;

import static de.uka.ilkd.key.nparser.format.KeyFileFormatter.format;

/**
 * The program interface of the KeY formatter utility.
 * You can run it using Gradle: {@code gradle :key.format:run}
 *
 * @author Alexander Weigl
 */
public class KeyFormatFacade {
    /**
     * Enables or disables the check for convergence of the formatting, i.e.,
     * {@code format(format(x)) == format(x)}.
     */
    public static boolean convergentCheck = false;

    private static final Logger LOGGER = LoggerFactory.getLogger(KeyFormatFacade.class);

    /**
     * Check if the given {@code file} is properly formatted.
     *
     * @param file path to an existing file
     * @return true iff the file is properly formatted
     * @throws IOException if the file does not exist or is not readable.
     */
    public static boolean checkFile(Path file) throws IOException {
        var formatted = format(CharStreams.fromPath(file));
        var content = Files.readString(file);
        return !content.equals(formatted);
    }


    /**
     * Reformat the given path and store it in {@code output}.
     * <p>
     * {@code} output is not written when an error occurred.
     *
     * @param input source file
     * @param output target file
     * @throws IOException file not found or not readable.
     */
    public static void formatSingleFile(Path input, Path output) throws IOException {
        var content = CharStreams.fromPath(input);
        try {
            var formatted = format(content);

            if (convergentCheck) {
                var secondInput = CharStreams.fromString(formatted);
                try {
                    if (!formatted.equals(format(secondInput))) {
                        LOGGER.error("{} | Formatter is not convergent on ", input);
                    }
                } catch (SyntaxErrorReporter.ParserException e) {
                    LOGGER.error("{} | Formatter produces rubbish", input);
                }
            }

            Files.writeString(output, formatted);
        } catch (SyntaxErrorReporter.ParserException e) {
            System.err.println(input + " | Failed to format");
        }
    }

    private static void formatSingleFileTo(Path input) throws IOException {
        formatSingleFile(input, input);
    }

    @Command(name = "format")
    private static class Format implements Callable<Integer> {
        @Parameters(arity = "1..*", description = "", paramLabel = "PATH")
        private List<Path> paths = new ArrayList<>();

        @Override
        public Integer call() throws IOException {
            var files = expandPaths(paths);

            for (var file : files) {
                try {
                    formatSingleFileTo(file);
                } catch (SyntaxErrorReporter.ParserException e) {
                    LOGGER.error("{} | Parser error", file, e);
                }
            }
            return 0;
        }
    }

    static List<Path> expandPaths(List<Path> paths) throws IOException {
        List<Path> files = new ArrayList<>(paths.size() * 128);
        for (var path : paths) {
            if (Files.isDirectory(path)) {
                try (final var walk = Files.walk(path)) {
                    files.addAll(walk.filter(Files::isRegularFile).toList());
                }
            } else {
                files.add(path);
            }
        }
        return files;
    }

    @Command(name = "check")
    private static class Check implements Callable<Integer> {
        @Parameters(arity = "1..*", description = "", paramLabel = "PATH")
        private List<Path> paths = new ArrayList<>();

        @Override
        public Integer call() throws IOException {
            var valid = true;
            var files = expandPaths(paths);
            for (Path file : files) {
                try {
                    if (checkFile(file)) {
                        valid = false;
                        LOGGER.warn("{} | File is not formatted properly", file);
                    }
                } catch (SyntaxErrorReporter.ParserException e) {
                    LOGGER.error("{} | Syntax errors in file", file, e);
                }
            }
            return valid ? 0 : 1;
        }
    }

    @Command()
    private static class Cmd {
    }

    public static void main(String[] args) {
        int exitCode = new CommandLine(new Cmd())
                .addSubcommand(new Format())
                .addSubcommand(new Check())
                .execute(args);
        System.exit(exitCode);
    }
}
