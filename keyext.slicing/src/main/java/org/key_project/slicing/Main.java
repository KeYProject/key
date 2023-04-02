package org.key_project.slicing;

import java.io.File;
import java.nio.file.Files;
import java.util.concurrent.atomic.AtomicReference;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.core.Log;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderControl;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.util.CommandLine;
import de.uka.ilkd.key.util.CommandLineException;

import org.key_project.slicing.analysis.AnalysisResults;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Simple command-line interface to the proof slicer.
 * Currently only displays the size of the proof slice computed using the dependency analysis
 * algorithm.
 *
 * @author Arne Keller
 */
public final class Main {

    /**
     * Help option.
     */
    private static final String HELP = "--help";

    /**
     * Logger.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(Main.class);

    private Main() {

    }

    /**
     * Main entry point. Parses CLI flags/options and performs the appropriate actions.
     *
     * @param args command-line arguments
     */
    public static void main(String[] args) {
        try {
            var cl = createCommandLine();
            cl.parse(args);
            Log.configureLogging(2);
            evaluateOptions(cl);
            var fileArguments = cl.getFileArguments();
            for (File file : fileArguments) {
                try {
                    processFile(file);
                } catch (Exception e) {
                    LOGGER.error("error occurred in slicing", e);
                }
            }
        } catch (ExceptionInInitializerError e) {
            LOGGER.error("D'oh! It seems that KeY was not built properly!", e);
            System.exit(777);
        } catch (CommandLineException e) {
            LOGGER.error("Error in parsing the command: {}", e.getMessage());
        }
    }

    private static void processFile(File proofFile) throws Exception {
        LOGGER.info("Processing proof: {}", proofFile.getName());
        GeneralSettings.noPruningClosed = false;
        AtomicReference<DependencyTracker> tracker = new AtomicReference<>();
        KeYEnvironment<?> environment =
            KeYEnvironment.load(JavaProfile.getDefaultInstance(), proofFile, null, null, null, null,
                null, proof -> {
                    tracker.set(new DependencyTracker(proof));
                }, true);
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

                Files.delete(saved.toPath());
            } finally {
                environment2.dispose();
            }
        } finally {
            environment.dispose();
        }
    }

    private static CommandLine createCommandLine() {
        var cl = new CommandLine();
        cl.setIndentation(3);
        cl.addSection("Using KeY's proof slicer");
        cl.addText("Usage: ./key [options] [filename]\n\n", false);
        cl.addSection("Options");
        cl.addOption(HELP, null, "display this text");
        // cl.addOption(OUTPUT, "<filename>", "output file (required)");
        return cl;
    }

    private static void evaluateOptions(CommandLine cl) {
        if (cl.getFileArguments().isEmpty()) {
            LOGGER.error("provide at least one proof to slice");
            System.exit(1);
        }
    }
}
