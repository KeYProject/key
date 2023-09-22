/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.java;

import java.io.IOException;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Stream;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Process builder that first checks whether a program is installed.
 *
 * @author Arne Keller
 */
public class CheckedProcessBuilder {
    public static final Logger LOGGER = LoggerFactory.getLogger(CheckedProcessBuilder.class);

    /**
     * The programs already checked.
     */
    private static final Set<String> CHECKED = new HashSet<>();
    /**
     * Installed programs.
     */
    private static final Set<String> AVAILABLE = new HashSet<>();
    /**
     * Program of this builder.
     */
    private final String program;

    /**
     * Create a new builder and check for the given program.
     *
     * @param program the program
     * @param programCheck program invocation used to check (e.g. --version)
     */
    public CheckedProcessBuilder(String program, String[] programCheck) {
        this.program = program;
        if (CHECKED.contains(program)) {
            return;
        }
        CHECKED.add(program);
        try {
            String[] check = Stream.concat(Stream.of(program), Arrays.stream(programCheck))
                    .toArray(String[]::new);
            new ProcessBuilder(check).start().waitFor();
            AVAILABLE.add(program);
        } catch (IOException | InterruptedException e) {
            // not available
            LOGGER.warn("{} is not available", program);
        }
    }

    /**
     * Start and wait for the program with the given argument list.
     * If the program is not available, no action is done.
     *
     * @param args arguments (without program name)
     * @throws IOException on start error (unlikely)
     * @throws InterruptedException on wait error
     */
    public void start(String... args) throws IOException, InterruptedException {
        if (args.length == 0) {
            throw new IllegalStateException("need program to execute");
        }
        if (AVAILABLE.contains(program)) {
            String[] fullArgs =
                Stream.concat(Stream.of(program), Arrays.stream(args)).toArray(String[]::new);
            new ProcessBuilder(fullArgs).start().waitFor();
        }
    }
}
