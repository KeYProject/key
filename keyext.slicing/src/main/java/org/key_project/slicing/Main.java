/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.List;
import java.util.Locale;
import java.util.concurrent.Callable;
import java.util.concurrent.atomic.AtomicReference;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.core.Log;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderControl;
import de.uka.ilkd.key.settings.GeneralSettings;

import org.key_project.slicing.analysis.AnalysisResults;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import picocli.CommandLine;
import picocli.CommandLine.Option;
import picocli.CommandLine.Parameters;

/**
 * Simple command-line interface to the proof slicer.
 * Currently only displays the size of the proof slice computed using the dependency analysis
 * algorithm.
 *
 * @author Arne Keller
 */
public final class Main implements Callable<Integer> {
    private static final Logger LOGGER = LoggerFactory.getLogger(Main.class);

    @Option(names = "--overwrite",
        description = "overwrite all files with their sliced counterpart")
    private boolean overwrite = false;

    @Parameters(arity = "*")
    private List<File> inputs = List.of();

    /**
     * Main entry point. Parses CLI flags/options and performs the appropriate actions.
     *
     * @param args command-line arguments
     */
    public static void main(String[] args) {
        Locale.setDefault(Locale.US);
        int exitCode = new CommandLine(new de.uka.ilkd.key.core.Main())
                .execute(args);
        System.exit(exitCode);
    }

    @Override
    public Integer call() throws Exception {
        Log.configureLogging(2);
        if (overwrite) {
            LOGGER.info("--overwrite given, writing files");
        }

        for (File file : inputs) {
            try {
                processFileOrDir(file.toPath(), overwrite);
            } catch (Exception e) {
                LOGGER.error("error occurred in slicing", e);
            }
        }
        return 0;
    }

    private void processFileOrDir(Path path, boolean overwrite) {
        var file = path.toFile();
        if (file.isFile()) {
            try {
                if (!path.toString().endsWith(".proof")) {
                    LOGGER.debug("Ignoring non proof file {}", path);
                    return;
                }
                processFile(file, overwrite);
            } catch (Exception e) {
                LOGGER.error("error occurred in slicing ", e);
            }
        } else if (file.isDirectory()) {
            try (var s = Files.newDirectoryStream(file.toPath())) {
                for (Path child : s) {
                    processFileOrDir(child, overwrite);
                }
            } catch (IOException e) {
                LOGGER.error("error walking dir ", e);
            }
        }
    }

    private void processFile(File proofFile, boolean overwrite) throws Exception {
        LOGGER.info("Processing proof: {}", proofFile.getName());
        GeneralSettings.noPruningClosed = false;
        AtomicReference<DependencyTracker> tracker = new AtomicReference<>();
        KeYEnvironment<?> environment =
            KeYEnvironment.load(JavaProfile.getDefaultInstance(), proofFile, null, null, null, null,
                null, proof -> tracker.set(new DependencyTracker(proof)), true);
        try {
            // get loaded proof
            Proof proof = environment.getLoadedProof();
            // analyze proof
            AnalysisResults results = tracker.get().analyze(true, false);
            // slice proof
            ProblemLoaderControl control = new DefaultUserInterfaceControl();
            File saved = SlicingProofReplayer
                    .constructSlicer(control, proof, results, null).slice();
            KeYEnvironment<?> environment2 =
                KeYEnvironment.load(JavaProfile.getDefaultInstance(), saved, null, null,
                    null, null, null, null, true);
            Proof slicedProof = environment2.getLoadedProof();

            try {
                LOGGER.info("Original proof: {} steps, {} branch(es)",
                    proof.countNodes() - proof.allGoals().size(), proof.countBranches());
                LOGGER.info("Sliced proof: {} steps, {} branch(es)",
                    slicedProof.countNodes() - slicedProof.allGoals().size(),
                    slicedProof.countBranches());

                if (overwrite) {
                    LOGGER.info("Saving sliced proof");
                    Files.move(saved.toPath(), proofFile.toPath(),
                        StandardCopyOption.REPLACE_EXISTING);
                } else {
                    Files.delete(saved.toPath());
                }
            } finally {
                environment2.dispose();
            }
        } finally {
            environment.dispose();
        }
    }
}
