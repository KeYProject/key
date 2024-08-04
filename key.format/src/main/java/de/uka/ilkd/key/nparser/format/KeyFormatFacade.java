package de.uka.ilkd.key.nparser.format;/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

import de.uka.ilkd.key.util.parsing.SyntaxErrorReporter;
import org.antlr.v4.runtime.CharStreams;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import picocli.CommandLine;
import picocli.CommandLine.Command;
import picocli.CommandLine.Parameters;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static de.uka.ilkd.key.nparser.format.KeYFileFormatter.format;

/**
 * The program interface of the KeY formatter utility.
 * You can run it using Gradle: {@code gradle :key.format:run}
 *
 * @author Alexander Weigl
 */
public class KeyFormatFacade {
    /**
     *
     */
    public static boolean CONVERGENT_CHECK = false;

    public static final Logger LOGGER = LoggerFactory.getLogger(KeyFormatFacade.class);

    /**
     * Reformat the given path and store it in {@code output}.
     * <p>
     * {@code} output is not written when an error occurred.
     *
     * @param input  source file
     * @param output target file
     * @throws IOException file not found or not readable.
     */
    public static void formatSingleFile(Path input, Path output) throws IOException {
        var content = CharStreams.fromPath(input);
        try {
            var formatted = format(content);

            if (CONVERGENT_CHECK) {
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

    private static void formatSingleFileTo(Path input, Path outputDir) throws IOException {
        var output = outputDir.resolve(input.getFileName());
        formatSingleFile(input, output);
    }

    public static boolean checkFile(Path file) throws IOException {
        var formatted = format(CharStreams.fromPath(file));
        var content = Files.readString(file);
        return !content.equals(formatted);
    }

    private static List<Path> expandPath(Path path) throws IOException {
        if (!Files.exists(path)) {
            throw new FileNotFoundException();
        }

        if (Files.isDirectory(path)) {
            try (Stream<Path> s = Files.walk(path)) {
                return s.collect(Collectors.toList());
            }
        } else {
            return Collections.singletonList(path);
        }
    }

    @Command(name = "format")
    private static class Format implements Callable<Integer> {
        @Parameters(arity = "1..*", description = "", paramLabel = "PATH")
        private List<Path> paths = new ArrayList<>();

        @Override
        public Integer call() {
            for (var path : paths) {
                try {
                    var files = expandPath(path);
                    for (Path file : files) {
                        try {
                            formatSingleFileTo(file, file);
                        } catch (SyntaxErrorReporter.ParserException e) {
                            LOGGER.error("{} | Parser error", path, e);
                        }
                    }
                } catch (IOException e) {
                    LOGGER.error("{} | could not read directory", path, e);
                }
            }
            return 0;
        }
    }

    @Command(name = "check")
    private static class Check implements Callable<Integer> {
        @Parameters(arity = "1..*", description = "", paramLabel = "PATH")
        private List<Path> paths = new ArrayList<>();

        @Override
        public Integer call() {
            var valid = true;
            for (Path path : paths) {
                try {
                    for (Path file : expandPath(path)) {
                        try {
                            if (checkFile(file)) {
                                valid = false;
                                LOGGER.warn("{} | File is not formatted properly", path);
                            }
                        } catch (SyntaxErrorReporter.ParserException e) {
                            LOGGER.error("{} | Syntax errors in file", path, e);
                        }
                    }
                } catch (IOException e) {
                    LOGGER.error("{} | could not read directory", path, e);
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
