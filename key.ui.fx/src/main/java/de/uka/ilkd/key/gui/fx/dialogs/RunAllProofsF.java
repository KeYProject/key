/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.dialogs;

import java.nio.file.Path;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * menu: MP5 — minimal JavaFX port of the Swing {@code RunAllProofsAction}
 * (key.ui/.../gui/actions/RunAllProofsAction.java), the QA feature shown in the "Prove" submenu
 * behind the {@code BULK_UI_TEST} feature flag. The Swing action maintains a whole <em>list</em>
 * of proof files (from a newline-separated file referenced by the {@link #ENV_VARIABLE}
 * environment variable, or the bundled {@code runallproofsui.txt}) and auto-proves each in turn;
 * this port keeps the smallest useful subset:
 * <ul>
 * <li>the proof file spec is read from the environment variable or (as a port convenience) the
 * system property {@value #ENV_VARIABLE} — Swing reads only the environment,</li>
 * <li>a spec ending in {@code .key} is loaded and auto-proved once by the caller
 * (load + auto mode, the summary of Swing's
 * {@code actionPerformed: ui.getProblemLoader(...).runSynchronously()} + {@code startAutoMode}
 * + {@code waitWhileAutoMode()});</li>
 * <li>any other spec (or none) yields a short usage/status message instead of the Swing whole
 * batch machinery ({@code // menu:} the multi-file batch loop and the odometer progress are not
 * ported).</li>
 * </ul>
 */
public final class RunAllProofsF {
    private static final Logger LOGGER = LoggerFactory.getLogger(RunAllProofsF.class);

    /**
     * Environment variable which points to a proof file to be run (Swing
     * {@code RunAllProofsAction.ENV_VARIABLE}).
     */
    public static final String ENV_VARIABLE = "KEY_RUNALLPROOFS_UI_FILE";

    private RunAllProofsF() {
    }

    /**
     * Resolves the proof file to auto-prove from {@link #ENV_VARIABLE} (environment variable,
     * then system property).
     *
     * @return the absolute proof file, or {@code null} when the variable is not set or does not
     *         name a {@code .key} file (Swing falls back to the bundled file list; the FX port
     *         has no bundled list and reports the usage message instead)
     */
    public static @Nullable Path proofToRun() {
        String spec = System.getenv(ENV_VARIABLE);
        if (spec == null || spec.isBlank()) {
            spec = System.getProperty(ENV_VARIABLE);
        }
        if (spec == null || spec.isBlank()) {
            return null;
        }
        Path path = Path.of(spec).toAbsolutePath();
        if (!path.toString().endsWith(".key")) {
            LOGGER.info("Run All Proofs: ignoring {}={} (no .key file)", ENV_VARIABLE, spec);
            return null;
        }
        return path;
    }

    /**
     * @return the usage message shown when {@link #proofToRun()} has nothing to do
     */
    public static String usageMessage() {
        return "Run All Proofs is active, but " + ENV_VARIABLE
            + " is not set to a .key file to auto-prove (e.g. export "
            + ENV_VARIABLE + "=/path/to/example.key).";
    }
}
