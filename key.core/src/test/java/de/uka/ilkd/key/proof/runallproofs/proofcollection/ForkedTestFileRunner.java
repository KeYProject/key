/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.uka.ilkd.key.proof.runallproofs.TestResult;
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.util.IOForwarder;

import org.junit.jupiter.api.Assertions;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.*;


/**
 * Executes KeY prover for a list of {@link TestFile}s in a separate process.
 *
 * @author Kai Wallisch
 */
public abstract class ForkedTestFileRunner implements Serializable {
    private static final Logger LOGGER = LoggerFactory.getLogger(ForkedTestFileRunner.class);

    private static final long serialVersionUID = 1L;


    private static Path getLocationOfSerializedTestFiles(Path tempDirectory) {
        return Paths.get(tempDirectory.toString(), "TestFiles.serialized");
    }

    private static Path getLocationOfSerializedException(Path tempDirectory) {
        return Paths.get(tempDirectory.toString(), "Exception.serialized");
    }

    private static Path getLocationOfSerializedTestResults(Path tempDirectory) {
        return Paths.get(tempDirectory.toString(), "TestResults.serialized");
    }

    /*
     * Converts a {@link Serializable} object into a byte array and stores it in a file at given
     * location.
     */
    private static void writeObject(Path path, Serializable s) throws IOException {

        try (ObjectOutputStream objectOutputStream =
            new ObjectOutputStream(Files.newOutputStream(path))) {
            objectOutputStream.writeObject(s);
        }
    }

    /**
     * Converts contents of a file back into an object.
     */
    private static <S> S readObject(Path path, Class<S> type)
            throws IOException, ClassNotFoundException {
        try (ObjectInputStream objectInputStream =
            new ObjectInputStream(Files.newInputStream(path))) {
            Object result = objectInputStream.readObject();
            return type.cast(result);
        }
    }

    /**
     * Process a single {@link TestFile} in a separate subprocess.
     */
    public static TestResult processTestFile(TestFile testFile, Path pathToTempDir)
            throws Exception {
        List<TestFile> files = List.of(testFile);
        return processTestFiles(files, pathToTempDir).get(0);
    }

    /**
     * Process a list of {@link TestFile}s in a separate subprocess.
     *
     * @param testFiles files to be tested
     * @param pathToTempDir a path to the temporary data directory
     */
    public static List<TestResult> processTestFiles(List<TestFile> testFiles, Path pathToTempDir)
            throws Exception {
        if (testFiles.isEmpty()) {
            return new ArrayList<>();
        }
        ProofCollectionSettings settings = testFiles.get(0).getSettings();

        writeObject(getLocationOfSerializedTestFiles(pathToTempDir),
            testFiles.toArray(new TestFile[0]));

        ProcessBuilder pb =
            new ProcessBuilder("java", "-classpath", System.getProperty("java.class.path"),
                // pass through the value of key.disregardSettings
                "-D" + PathConfig.DISREGARD_SETTINGS_PROPERTY + "="
                    + Boolean.getBoolean(PathConfig.DISREGARD_SETTINGS_PROPERTY));
        List<String> command = pb.command();

        // TODO make sure no injection happens here?
        String forkMemory = settings.getForkMemory();
        if (forkMemory != null) {
            command.add("-Xmx" + forkMemory);
        }

        String debugPort = settings.getForkDebugPort();
        if (debugPort != null) {
            String suspend = "n";
            if (debugPort.startsWith("wait:")) {
                debugPort = debugPort.substring(5);
                suspend = "y";
            }
            int port;
            try {
                port = Integer.parseInt(debugPort);
            } catch (NumberFormatException e) {
                throw new IOException("port number must be a number");
            }
            command.addAll(Arrays.asList("-Xdebug", "-Xnoagent", "-Djava.compiler=NONE",
                "-Xrunjdwp:transport=dt_socket,server=y,suspend=" + suspend + ",address=" + port));
        }

        command.add(ForkedTestFileRunner.class.getName());
        command.add(pathToTempDir.toString());

        Process process = pb.start();
        IOForwarder.forward(process);
        process.waitFor();
        assertEquals(0, process.exitValue(),
            "Executed process terminated with non-zero exit value.");

        /*
         * Check if an exception occured and rethrow it if one occured.
         */
        Path exceptionFile = getLocationOfSerializedException(pathToTempDir);
        if (exceptionFile.toFile().exists()) {
            Throwable t = ForkedTestFileRunner.readObject(exceptionFile, Throwable.class);
            Assertions.fail("Subprocess returned exception", t);
        }

        /*
         * Read serialized list of test results and return.
         */
        Path testResultsFile = getLocationOfSerializedTestResults(pathToTempDir);
        assertTrue(testResultsFile.toFile().exists(),
            "File containing serialized test results not present.");
        TestResult[] array = ForkedTestFileRunner.readObject(testResultsFile, TestResult[].class);

        return Arrays.asList(array);
    }

    public static void main(String[] args) throws IOException {
        /*
         * Check for existence of temp dir before entering try-catch block. Throwables occuring in
         * this block are written to temp dir, so its existence needs to be confirmed beforehand.
         */
        Path tempDirectory = Paths.get(args[0]);
        if (!tempDirectory.toFile().exists()) {
            throw new Error("RunAllProofs temporary directory does not exist: " + tempDirectory);
        }

        boolean error = false;
        try {
            TestFile[] testFiles = ForkedTestFileRunner
                    .readObject(getLocationOfSerializedTestFiles(tempDirectory), TestFile[].class);
            installTimeoutWatchdog(testFiles[0].getSettings(), tempDirectory);
            ArrayList<TestResult> testResults = new ArrayList<>();
            for (TestFile testFile : testFiles) {
                try {
                    testResults.add(testFile.runKey());
                } catch (Exception e) {
                    error = true;
                    LOGGER.warn("Run failed", e);
                }
            }
            writeObject(getLocationOfSerializedTestResults(tempDirectory),
                testResults.toArray(new TestResult[0]));
        } catch (Throwable t) {
            try {
                writeObject(getLocationOfSerializedException(tempDirectory), t);
            } catch (NotSerializableException e) {
                // There are cases when exceptions refer to objects that cannot be serialized ...
                // then save the stacktrace at least
                Exception subst = new Exception(t.getMessage());
                subst.setStackTrace(t.getStackTrace());
                writeObject(getLocationOfSerializedException(tempDirectory), subst);
            }
        }

        if (error) {
            fail("Exception during the execution of proofs. See log for more details.");
        }
    }

    /**
     * Launches a timeout-thread acting as a watchdog over this forked instance.
     * <p>
     * If a time is specified in the settings, a fresh daemon thread is started which terminates
     * this instance after the specified time has elapsed.
     * <p>
     * If no timeout has been specified, no thread is launched.
     *
     * @param settings the (non-null) settings to take the timeout from.
     * @param tempDirectory
     */
    private static void installTimeoutWatchdog(ProofCollectionSettings settings,
            final Path tempDirectory) {

        String timeoutString = settings.getForkTimeout();
        if (timeoutString == null) {
            return;
        }

        final boolean verbose = settings.getVerboseOutput();

        final int timeout;
        try {
            timeout = Integer.parseInt(timeoutString);
        } catch (NumberFormatException ex) {
            throw new RuntimeException(
                "The setting forkTimeout requires an integer, not " + timeoutString, ex);
        }

        if (timeout <= 0) {
            throw new RuntimeException(
                "The setting forkTimeout requires a positive integer, not " + timeoutString);
        }

        Thread t = new Thread("Timeout watchdog") {
            @Override
            public void run() {
                try {
                    if (verbose) {
                        LOGGER.info("Timeout watcher launched (" + timeout + " secs.)");
                    }
                    Thread.sleep(timeout * 1000L);
                    InterruptedException ex =
                        new InterruptedException("forkTimeout (" + timeout + "sec.) elapsed");
                    writeObject(getLocationOfSerializedException(tempDirectory), ex);
                    // TODO consider something other than 0 here
                    if (verbose) {
                        LOGGER.info("Process timed out");
                    }
                    System.exit(0);
                } catch (Exception ex) {
                    LOGGER.warn("The watchdog has been interrupted or failed. Timeout cancelled.",
                        ex);
                }
            }
        };
        t.setDaemon(true);
        t.start();
    }

}
