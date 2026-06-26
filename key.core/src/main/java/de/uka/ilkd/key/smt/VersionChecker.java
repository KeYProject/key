/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.concurrent.TimeUnit;

import org.jspecify.annotations.Nullable;

/**
 * Little helper class that helps to check for the version of a solver. Mainly it provides a method
 * that starts the solver using certain parameters in order to obtain the version of that solver.
 */
public class VersionChecker {
    public static final VersionChecker INSTANCE = new VersionChecker();

    /**
     * Upper bound for how long we wait for the solver to print its version and exit. Generous on
     * purpose: this runs once per solver, and a too-small bound made version detection flaky on
     * loaded CI machines (cold process start &gt; 1s).
     */
    private static final long MAX_DELAY = 10_000;

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
            // Wait for the process to actually finish before reading. Previously the code gated on
            // BufferedReader.ready(), which returns false whenever the output has not been buffered
            // yet (a race under load) and then reported "no version". Honor the timeout instead and
            // read only after the process has terminated, so the output is already available.
            if (!p.waitFor(MAX_DELAY, TimeUnit.MILLISECONDS)) {
                p.destroyForcibly();
                return null;
            }
            try (BufferedReader r = new BufferedReader(
                new InputStreamReader(p.getInputStream(), StandardCharsets.UTF_8))) {
                // The process has exited, so this read does not block.
                return r.readLine();
            }
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return null;
        } catch (IOException e) {
            // Solver not found / not executable: treat as "version unknown" rather than crashing
            // the caller.
            return null;
        } finally {
            if (p != null && p.isAlive()) {
                p.destroyForcibly();
            }
        }
    }
}
