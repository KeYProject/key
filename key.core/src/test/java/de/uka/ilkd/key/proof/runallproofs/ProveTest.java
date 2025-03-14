/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.runallproofs;

import java.io.File;
import java.io.IOException;
import java.util.List;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.StatisticsFile;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.TestProperty;
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.settings.ProofSettings;

import org.key_project.util.collection.Pair;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.*;


/**
 * This class provides an API for running proves in JUnit test cases.
 * <p>
 * It is not intended to use this class outside of JUnit tests. The API mimics the same behavior as
 * run-all-proves. So {@link #assertLoadability(String)}, {@link #assertLoadability(String)}, and
 * {@link #assertUnProvability(String)} correspond to the commands in the proof collection file.
 * <p>
 * Use the the member variables to configure the execution. Their meaning is identical to the
 * variable in {@link de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollection}.
 * <p>
 * This class is used by generated unit tests from the proof collections.
 *
 * @author Alexander Weigl
 * @version 1 (12.07.19)
 * @see GenerateUnitTests
 */
public class ProveTest {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProveTest.class);

    protected final boolean verbose = Boolean.getBoolean("prooftests.verbose");
    protected String baseDirectory = "";
    protected String statisticsFile = "tmp.csv";
    protected String name = "unnamed_tests";
    protected boolean reloadEnabled = false;
    protected String tempDir = "/tmp";
    protected String globalSettings = "";
    protected String localSettings = "";
    private StatisticsFile statistics;

    protected void assertProvability(String file) throws Exception {
        runKey(file, TestProperty.PROVABLE);
    }

    protected void assertUnProvability(String file) throws Exception {
        runKey(file, TestProperty.NOTPROVABLE);
    }

    protected void assertLoadability(String file) throws Exception {
        runKey(file, TestProperty.LOADABLE);
    }

    protected void assertUnLoadability(String file) throws Exception {
        runKey(file, TestProperty.NOTLOADABLE);
    }

    private void runKey(String file, TestProperty testProperty) throws Exception {
        File keyFile = new File(file);

        // a name for this run. helps to find it in the mass of logger
        final var caseId = "%s|%d".formatted(keyFile.getName(), keyFile.hashCode());

        LOGGER.info("{}: Run Test: {} with {}", caseId, file, testProperty);

        // Initialize KeY settings.
        ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(globalSettings);
        if (localSettings != null && !localSettings.isEmpty()) {
            // local settings must be complete to have desired effect
            ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(localSettings);
        }

        LOGGER.info("({}) Active Settings: {}", caseId,
            ProofSettings.DEFAULT_SETTINGS.settingsToString());

        assertTrue(keyFile.exists(), "File " + keyFile + " does not exists");

        // File that the created proof will be saved to.
        File proofFile = new File(keyFile.getAbsolutePath() + ".proof");

        LOGGER.info("({}) Proof will be saved to: {}", caseId, proofFile);

        KeYEnvironment<DefaultUserInterfaceControl> env = null;
        Proof loadedProof = null;
        boolean success;
        try {
            LOGGER.info("({}) Start proving", caseId);
            // Initialize KeY environment and load proof.
            var pair = load(keyFile);
            LOGGER.info("({}) Proving done", caseId);
            env = pair.first;
            var script = pair.second;
            loadedProof = env.getLoadedProof();

            AbstractProblemLoader.ReplayResult replayResult = env.getReplayResult();
            if (replayResult.hasErrors() && verbose) {
                LOGGER.info("({}) {} Error(s) while loading", caseId, replayResult.getErrorList());
                for (Throwable error : replayResult.getErrorList()) {
                    LOGGER.info("({}) Error", caseId, error);
                }
            }

            if (testProperty == TestProperty.NOTLOADABLE) {
                assertTrue(replayResult.hasErrors(),
                    "Loading problem file succeeded but it shouldn't");
                success = true;
            } else {
                assertFalse(replayResult.hasErrors(), "Loading problem file failed");

                // For a reload test we are done at this point. Loading was successful.
                if (testProperty == TestProperty.LOADABLE) {
                    success = true;
                    LOGGER.info("({}) Success: loaded", caseId);
                } else {
                    autoMode(env, loadedProof, script);
                    boolean closed = loadedProof.closed();
                    success = (testProperty == TestProperty.PROVABLE) == closed;
                    LOGGER.info("({}) Finished proof: {}", caseId,
                        (closed ? "closed." : "open goal(s)"));
                    appendStatistics(loadedProof, keyFile);
                    if (success) {
                        reload(proofFile, loadedProof);
                    }
                }
            }
        } finally {
            if (loadedProof != null) {
                loadedProof.dispose();
            }
            if (env != null) {
                env.dispose();
            }
        }

        String message = String.format("(%s) %sVerifying property \"%s\"%sfor file: %s",
            caseId,
            success ? "pass: " : "FAIL: ", testProperty.toString().toLowerCase(),
            success ? " was successful " : " failed ", keyFile);

        if (!success) {
            fail(message);
        }
    }

    /**
     * Override this method in order to change reload behaviour.
     */
    private void reload(File proofFile, Proof loadedProof) throws Exception {
        if (reloadEnabled) {
            System.err.println("Test reloadability.");
            // Save the available proof to a temporary file.
            ProofSaver.saveToFile(proofFile, loadedProof);
            boolean reloadedClosed = reloadProof(proofFile);

            assertEquals(loadedProof.closed(), reloadedClosed,
                "Reloaded proof did not close: " + proofFile);
            debugOut("... success: reloaded.");
        }
    }

    /**
     * By overriding this method we can change the way how we invoke automode, for instance if we
     * want to use a different strategy.
     */
    private void autoMode(KeYEnvironment<DefaultUserInterfaceControl> env, Proof loadedProof,
            KeyAst.ProofScript script) throws Exception {
        // Run KeY prover.
        if (script == null) {
            // auto mode
            env.getProofControl().startAndWaitForAutoMode(loadedProof);
        } else {
            // ... script
            ProofScriptEngine pse = new ProofScriptEngine(script);
            pse.execute(env.getUi(), env.getLoadedProof());
        }
    }

    /*
     * has resemblances with KeYEnvironment.load ...
     */
    private Pair<KeYEnvironment<DefaultUserInterfaceControl>, KeyAst.ProofScript> load(File keyFile)
            throws ProblemLoaderException {
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(keyFile);
        return new Pair<>(env, env.getProofScript());
    }

    /**
     * Reload proof that was previously saved at the location corresponding to the given
     * {@link File} object.
     *
     * @param proofFile File that contains the proof that will be (re-)loaded.
     */
    private boolean reloadProof(File proofFile) throws Exception {
        /*
         * Reload proof and dispose corresponding KeY environment immediately afterwards. If no
         * exception is thrown it is assumed that loading works properly.
         */
        KeYEnvironment<DefaultUserInterfaceControl> proofLoadEnvironment = null;
        Proof reloadedProof = null;
        try {
            proofLoadEnvironment = KeYEnvironment.load(proofFile);

            AbstractProblemLoader.ReplayResult result = proofLoadEnvironment.getReplayResult();
            if (result.hasErrors()) {
                List<Throwable> errorList = result.getErrorList();
                for (Throwable ex : errorList) {
                    LOGGER.error("Error", ex);
                }
                throw errorList.get(0);
            }

            reloadedProof = proofLoadEnvironment.getLoadedProof();
            return reloadedProof.closed();
        } catch (Throwable t) {
            throw new Exception(
                "Exception while loading proof (see cause for details): " + proofFile, t);
        } finally {
            if (reloadedProof != null) {
                reloadedProof.dispose();
            }
            if (proofLoadEnvironment != null) {
                proofLoadEnvironment.dispose();
            }
        }
    }

    protected StatisticsFile getStatisticsFile() throws IOException {
        if (!statisticsFile.isEmpty()) {
            if (statistics == null) {
                statistics = new StatisticsFile(new File(statisticsFile));
                statistics.setUp(false);
            }
            return statistics;
        }
        return null;
    }

    private void appendStatistics(Proof loadedProof, File keyFile) {
        // Write statistics.
        try {
            StatisticsFile statisticsFile = getStatisticsFile();
            if (statisticsFile != null) {
                statisticsFile.appendStatistics(loadedProof, keyFile);
            }
        } catch (IOException e) {
            LOGGER.warn("Failed to append stats", e);
        }
    }

    private void debugOut(String format, Object... args) {
        if (verbose) {
            System.err.format(format, args);
        }
    }
}
