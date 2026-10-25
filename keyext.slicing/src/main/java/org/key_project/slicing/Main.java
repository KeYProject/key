/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
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

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
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
@NullMarked
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
        if (Files.isRegularFile(path)) {
            try {
                if (!path.toString().endsWith(".proof")) {
                    LOGGER.debug("Ignoring non proof file {}", path);
                    return;
                }
                processFile(path, overwrite);
            } catch (Exception e) {
                LOGGER.error("error occurred in slicing ", e);
            }
        } else if (Files.isDirectory(path)) {
            try (var s = Files.newDirectoryStream(path)) {
                for (Path child : s) {
                    processFileOrDir(child, overwrite);
                }
            } catch (IOException e) {
                LOGGER.error("error walking dir ", e);
            }
        }
    }

    private void processFile(Path proofFile, boolean overwrite) throws Exception {
        Path fileName = proofFile.getFileName();
        if (fileName == null) {
            throw new NullPointerException("No file name for proof file " + proofFile + ".");
        }
        LOGGER.info("Processing proof: {}", fileName);
        GeneralSettings.noPruningClosed = false;
        AtomicReference<@Nullable DependencyTracker> tracker = new AtomicReference<>();
        KeYEnvironment<?> environment =
            KeYEnvironment.load(JavaProfile.getDefaultInstance(), proofFile, null, null, null, null,
                null, proof -> tracker.set(new DependencyTracker(proof)), true);
        try {
            // get loaded proof
            Proof proof = environment.getLoadedProof();
            if (proof == null) {
                throw new NullPointerException("No proof loaded from " + proofFile + ".");
            }
            // analyze proof
            DependencyTracker dependencyTracker = tracker.get();
            if (dependencyTracker == null) {
                throw new NullPointerException(
                    "No dependency tracker set while loading the proof " + proofFile + ".");
            }
            AnalysisResults results = dependencyTracker.analyze(true, false);
            if (results == null) {
                throw new NullPointerException("No analysis results for the loaded proof.");
            }
            // slice proof
            ProblemLoaderControl control = new DefaultUserInterfaceControl();
            Path saved = SlicingProofReplayer
                    .constructSlicer(control, proof, results, null).slice();
            KeYEnvironment<?> environment2 =
                KeYEnvironment.load(JavaProfile.getDefaultInstance(), saved, null, null,
                    null, null, null, null, true);
            Proof slicedProof = environment2.getLoadedProof();
            if (slicedProof == null) {
                throw new NullPointerException("No proof loaded from the sliced proof " + saved
                    + ".");
            }

            try {
                LOGGER.info("Original proof: {} steps, {} branch(es)",
                    proof.countNodes() - proof.allGoals().size(), proof.countBranches());
                LOGGER.info("Sliced proof: {} steps, {} branch(es)",
                    slicedProof.countNodes() - slicedProof.allGoals().size(),
                    slicedProof.countBranches());

                if (overwrite) {
                    LOGGER.info("Saving sliced proof");
                    Files.move(saved, proofFile,
                        StandardCopyOption.REPLACE_EXISTING);
                } else {
                    Files.delete(saved);
                }
            } finally {
                environment2.dispose();
            }
        } finally {
            environment.dispose();
        }
    }
}
