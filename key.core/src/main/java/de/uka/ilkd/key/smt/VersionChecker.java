/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.concurrent.TimeUnit;
import javax.annotation.Nullable;

/**
 * Little helper class that helps to check for the version of a solver. Mainly it provides a method
 * that starts the solver using certain parameters in order to obtain the version of that solver.
 */
public class VersionChecker {
    public static final VersionChecker INSTANCE = new VersionChecker();

    private static final long MAX_DELAY = 1000;

    /**
     *
     * @param command to start the solver process
     * @param parameter version parameter of the solver
     * @return the returned version String of the solver, if any was returned, null otherwise
     */
    public @Nullable String getVersionFor(String command, String parameter) {
        ProcessBuilder pb = new ProcessBuilder(command, parameter);
        Process p = null;
        try {
            p = pb.start();
            p.waitFor(MAX_DELAY, TimeUnit.MILLISECONDS);
            try (BufferedReader r = new BufferedReader(
                new InputStreamReader(p.getInputStream(), StandardCharsets.UTF_8))) {
                // Avoid potential blocking by the buffer's readLine()
                if (!r.ready()) {
                    return null;
                }
                String line = r.readLine();
                // TODO weigl for Java 11 use "p.destroyForcibly();"
                return line;
            }
        } catch (Exception e) {
            throw new RuntimeException(e);
        } finally {
            if (p != null && p.isAlive()) {
                p.destroy();
            }
        }
    }
}
