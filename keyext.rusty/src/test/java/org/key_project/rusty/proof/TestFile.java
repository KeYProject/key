/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.util.List;

import org.key_project.rusty.control.KeYEnvironment;
import org.key_project.rusty.proof.io.AbstractProblemLoader.ReplayResult;
import org.key_project.rusty.proof.io.ProblemLoaderException;
import org.key_project.rusty.proof.io.ProofSaver;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class TestFile {
    private final TestProperty testProperty;
    private final String path;
    private final ProofCollectionSettings settings;

    /**
     * In order to ensure that the implementation is independent of working directory, this method
     * can be used to return an absolute {@link File} object.
     *
     * @param baseDirectory Base directory that will be used as start location in case given path
     *        name is a relative path.
     * @param pathName Path whose associated {@link File} object will be returned.
     * @return {@link File} object pointing to given path name relative to given base directory.
     */
    static File getAbsoluteFile(File baseDirectory, String pathName) {

        /*
         * Caller of this method must provide an absolute path as base directory.
         */
        if (!baseDirectory.isAbsolute()) {
            throw new RuntimeException("Expecting an absolute path but found: " + baseDirectory);
        }

        if (!baseDirectory.isDirectory()) {
            throw new RuntimeException(
                "Given file system location is not a directory: " + baseDirectory);
        }

        /*
         * Initial directory is ignored in case provided path name is absolute.
         */
        File tmp = new File(pathName);
        File ret = tmp.isAbsolute() ? tmp : new File(baseDirectory, pathName);

        /*
         * Resulting file object should be absolute. This is just a safety check.
         */
        assert ret.isAbsolute() : "Expecting an absolute path but found: " + ret;

        return ret;
    }

    protected TestFile(TestProperty testProperty, String path, ProofCollectionSettings settings)
            throws IOException {
        this.path = path;
        this.testProperty = testProperty;
        this.settings = settings;
        getKeYFile();
    }

    /**
     * Returns a {@link File} object that points to the .key file that will be tested.
     *
     * @throws IOException Is thrown in case given .key-file is not a directory or does not exist.
     */
    public File getKeYFile() throws IOException {
        File baseDirectory = settings.getGroupDirectory();
        File keyFile = getAbsoluteFile(baseDirectory, path);

        if (keyFile.isDirectory()) {
            String exceptionMessage =
                "Expecting a file, but found a directory: " + keyFile.getAbsolutePath();
            throw new IOException(exceptionMessage);
        }

        if (!keyFile.exists()) {
            String exceptionMessage = "The given file does not exist: " + keyFile.getAbsolutePath();
            throw new IOException(exceptionMessage);
        }

        return keyFile;
    }

    private TestResult getRunAllProofsTestResult(OutputCatcher catcher, boolean success)
            throws IOException {
        String closing = String.format("%s: Verifying property \"%s\"%sfor file: %s",
            success ? "pass" : "FAIL", testProperty.toString().toLowerCase(),
            success ? " was successful " : " failed ", getKeYFile().toString());
        return new TestResult(catcher.getOutput() + "\n" + closing, success);
    }

    /**
     * Use KeY to verify that given {@link #testProperty} holds for KeY file that is at file system
     * location specified by {@link #path} string.
     *
     * @return Returns a {@link TestResult} object, which consists of a boolean value indicating
     *         whether test run was successful and a message string that can be printed out on
     *         command line to inform the user about the test result.
     * @throws Exception Any exception that may occur during KeY execution will be converted into an
     *         {@link Exception} object with original exception as cause.
     */
    public TestResult runKey() throws Exception {
        try (var catched = new OutputCatcher()) { // now everything System.out stuff will be also
            // caught
            boolean verbose = settings.getVerboseOutput();

            // Initialize KeY settings.
            // String gks = settings.getGlobalKeYSettings();
            // ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(gks);
            // String lks = settings.getLocalKeYSettings();
            // ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(lks);

            // Name resolution for the available KeY file.
            File keyFile = getKeYFile();
            if (verbose) {
                // LOGGER.info("Now processing file {}", keyFile);
            }
            // File that the created proof will be saved to.
            File proofFile = new File(keyFile.getAbsolutePath() + ".proof");

            KeYEnvironment env = null;
            Proof loadedProof = null;
            boolean success;
            try {
                // Initialize KeY environment and load proof.
                env = load(keyFile);
                loadedProof = env.getLoadedProof();
                ReplayResult replayResult;

                if (testProperty == TestProperty.NOT_LOADABLE) {
                    try {
                        replayResult = env.getReplayResult();
                    } catch (Throwable t) {
                        // LOGGER.info("... success: loading failed");
                        return getRunAllProofsTestResult(catched, true);
                    }
                    assertTrue(replayResult.hasErrors(),
                        "Loading problem file succeeded but it shouldn't");
                    // LOGGER.info("... success: loading failed");
                    return getRunAllProofsTestResult(catched, true);
                }

                replayResult = env.getReplayResult();
                if (replayResult.hasErrors() && verbose) {
                    // LOGGER.warn("... error(s) while loading");
                    List<Throwable> errors = replayResult.getErrorList();
                    for (int i = 0; i < errors.size(); i++) {
                        Throwable error = errors.get(i);
                        // LOGGER.warn("Error " + (i + 1) + ":", error);
                    }
                }

                assertFalse(replayResult.hasErrors(), "Loading problem file failed");

                // For a reload test we are done at this point. Loading was successful.
                if (testProperty == TestProperty.LOADABLE) {
                    if (verbose) {
                        // LOGGER.info("... success: loaded");
                    }
                    return getRunAllProofsTestResult(catched, true);
                }

                // autoMode(env, loadedProof, script);

                if (testProperty == TestProperty.PROVABLE
                        || testProperty == TestProperty.NOT_PROVABLE) {
                    ProofSaver.saveToFile(new File(keyFile.getAbsolutePath() + ".save.proof"),
                        loadedProof);
                }
                boolean closed = loadedProof.closed();
                success = (testProperty == TestProperty.PROVABLE) == closed;
                if (verbose) {
                    // LOGGER.info("... finished proof: " + (closed ? "closed." : "open goal(s)"));
                }

                // Write statistics.
                StatisticsFile statisticsFile = settings.getStatisticsFile();
                if (statisticsFile != null) {
                    statisticsFile.appendStatistics(loadedProof, keyFile);
                }

                /*
                 * Testing proof reloading now. Saving and reloading proof only in case it was
                 * closed
                 * and test property is PROVABLE.
                 */
                reload(verbose, proofFile, loadedProof, success);
            } catch (Throwable t) {
                if (verbose) {
                    // LOGGER.debug("Exception", t);
                }
                throw t;
            } finally {
                if (loadedProof != null) {
                    loadedProof.dispose();
                }
                if (env != null) {
                    env.dispose();
                }
            }
            return getRunAllProofsTestResult(catched, success);
        }
    }

    /**
     * Override this method in order to change reload behaviour.
     */
    protected void reload(boolean verbose, File proofFile, Proof loadedProof, boolean success)
            throws Exception {
        if (settings.reloadEnabled() && (testProperty == TestProperty.PROVABLE) && success) {
            // Save the available proof to a temporary file.
            ProofSaver.saveToFile(proofFile, loadedProof);
            reloadProof(proofFile);
            if (verbose) {
                // LOGGER.debug("... success: reloaded.");
            }
        }
    }

    private KeYEnvironment load(
            File keyFile) throws ProblemLoaderException {
        return KeYEnvironment.load(keyFile);
    }

    /**
     * Reload proof that was previously saved at the location corresponding to the given
     * {@link File} object.
     *
     * @param proofFile File that contains the proof that will be (re-)loaded.
     */
    private void reloadProof(File proofFile) throws Exception {
        /*
         * Reload proof and dispose corresponding KeY environment immediately afterwards. If no
         * exception is thrown it is assumed that loading works properly.
         */
        KeYEnvironment proofLoadEnvironment = null;
        Proof reloadedProof = null;
        try {
            proofLoadEnvironment = KeYEnvironment.load(proofFile);

            ReplayResult result = proofLoadEnvironment.getReplayResult();

            if (result.hasErrors()) {
                List<Throwable> errorList = result.getErrorList();
                for (Throwable ex : errorList) {
                    // LOGGER.warn("Replay exception", ex);
                }
                throw errorList.get(0);
            }

            reloadedProof = proofLoadEnvironment.getLoadedProof();

            List<Integer> goalsSerials = reloadedProof
                    .openGoals()
                    .stream()
                    .map(s -> s.getNode().getSerialNr())
                    .limit(10)
                    .toList();
            assertTrue(reloadedProof.closed(),
                "Reloaded proof did not close: " + proofFile + ", open goals were " + goalsSerials
                    + ", replay status: " + result.getStatus());
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

    public ProofCollectionSettings getSettings() {
        return settings;
    }

    public TestProperty getTestProperty() {
        return testProperty;
    }

    private static class OutputCatcher implements AutoCloseable {
        private final ByteArrayOutputStream sink = new ByteArrayOutputStream(4096);
        private final PrintStream shadow = new PrintStream(sink);

        private final PrintStream stdout = System.out;

        public OutputCatcher() {
            System.setOut(new PrintStream(new TeeOutputStream(shadow, stdout)));
        }

        @Override
        public void close() {
            System.setOut(stdout);
        }

        public String getOutput() {
            return sink.toString(StandardCharsets.UTF_8);
        }
    }

    public static class TeeOutputStream extends OutputStream {
        private final PrintStream a, c;

        public TeeOutputStream(PrintStream a, PrintStream b) {
            this.a = a;
            this.c = b;
        }

        @Override
        public void write(int b) throws IOException {
            this.a.write(b);
            this.c.write(b);
        }

        @Override
        public void write(byte[] b) throws IOException {
            this.a.write(b);
            this.c.write(b);
        }

        @Override
        public void write(byte[] b, int off, int len) throws IOException {
            a.write(b, off, len);
            c.write(b, off, len);
        }

        @Override
        public void flush() {
            a.flush();
            c.flush();
        }

        @Override
        public void close() throws IOException {
            a.close();
            c.close();
        }
    }
}
