/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.core.fx;

import java.nio.file.Path;
import java.util.List;
import java.util.Locale;
import java.util.concurrent.Callable;

import de.uka.ilkd.key.gui.fx.MainApplication;
import de.uka.ilkd.key.prover.impl.ParallelProver;
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import picocli.CommandLine;
import picocli.CommandLine.Option;
import picocli.CommandLine.Parameters;

/**
 * The main entry point of the JavaFX user interface (key.ui.fx).
 * <p>
 * This is the counter-part of {@code de.uka.ilkd.key.core.Main} in the Swing module
 * {@code key.ui}. It mirrors the command line interface of that class; the interactive mode
 * starts the JavaFX {@link MainApplication}, while the headless auto mode is planned for a
 * later milestone.
 */
public final class MainEx implements Callable<Integer> {
    private static final Logger LOGGER = LoggerFactory.getLogger(MainEx.class);

    /**
     * flag whether the automatic prove procedure should be started after initialisation without
     * GUI
     */
    @Option(names = "--auto",
        description = "start automatic prove procedure after initialisation without GUI (not yet "
            + "implemented in key.ui.fx)")
    private boolean auto = false;

    /**
     * Number of worker threads for the multi-core prover. A value &gt;= 1 enables the multi-core
     * prover (capped at the available processors); 0 leaves the persisted prover-mode setting
     * untouched (single-core by default).
     */
    @Option(names = "--threads", paramLabel = "INT",
        description = "run automatic proof search on the multi-core prover with INT worker threads "
            + "(>= 1, capped at the available processors). Omit for the single-core prover. "
            + "The single-core-only features (proof caching, slicing, merge rule) are off under "
            + "multi-worker runs (more than one worker); note that proof caching and slicing do "
            + "not record parallel runs even with a single worker.")
    private int proverThreads = 0;

    /**
     * Lists all features currently marked as experimental. Unless invoked with command line
     * option --experimental, those will be deactivated.
     */
    @Deprecated(since = "2.13.0")
    @Option(names = "--experimental", description = "switch experimental features on")
    private boolean experimental = false;

    /**
     * The file names provided on the command line.
     */
    @Parameters(arity = "*")
    private List<Path> inputFiles = List.of();

    public static void main(String[] args) {
        Locale.setDefault(Locale.US);

        int exitCode = new CommandLine(new MainEx()).execute(args);
        System.exit(exitCode);
    }

    @Override
    public Integer call() {
        // weigl: the configuration folder is not fixed anymore since v3.0
        LOGGER.info("The configuration folder is here {}", PathConfig.currentPaths.keyConfigDir);

        if (experimental) {
            LOGGER.info("Running in experimental mode ...");
            ProofIndependentSettings.DEFAULT_INSTANCE.getFeatureSettings().setActivateAll(true);
        }

        if (proverThreads >= 1) {
            // Apply --threads as a TRANSIENT process-scoped override via system properties,
            // mirroring the Swing Main: mutating GeneralSettings would fire a PropertyChange
            // that ProofIndependentSettings turns into saveSettings(), permanently rewriting
            // the user's persisted prover mode from a one-off CLI run.
            int workers = Math.min(proverThreads, Runtime.getRuntime().availableProcessors());
            System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
            System.setProperty(ParallelProver.THREADS_PROPERTY, Integer.toString(workers));
        }

        if (auto) {
            // Headless proving (ConsoleUserInterfaceControl port) is a later milestone.
            LOGGER.error("Auto mode (--auto) is not yet implemented in key.ui.fx. "
                + "Please use the Swing UI (module key.ui) for headless proving, "
                + "or run key.ui.fx without --auto.");
            return -1;
        }

        if (!inputFiles.isEmpty()) {
            LOGGER.warn("Loading problem files from the command line is not yet implemented in "
                + "key.ui.fx (planned for a later milestone): {}", inputFiles);
        }

        MainApplication.launch(MainApplication.class, new String[0]);
        return 0;
    }
}
