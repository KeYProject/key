package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.uka.ilkd.key.proof.runallproofs.TestResult;

/**
 * Executes KeY prover for a list of {@link TestFile}s in a separate process.
 * 
 * @author Kai Wallisch
 *
 */
public abstract class ForkedTestFileRunner implements Serializable {

    private static final String FORK_TIMEOUT_KEY = "forkTimeout";

   private static Path getLocationOfSerializedTestFiles(Path tempDirectory) {
      return Paths.get(tempDirectory.toString(), "TestFiles.serialized");
   }

   private static Path getLocationOfSerializedException(Path tempDirectory) {
      return Paths.get(tempDirectory.toString(), "Exception.serialized");
   }

   private static Path getLocationOfSerializedTestResults(Path tempDirectory) {
      return Paths.get(tempDirectory.toString(), "TestResults.serialized");
   }

   private static Path getLocationOfSerializedProofCollectionSettings(
         Path tempDirectory) {
      return Paths.get(tempDirectory.toString(),
            "ProofCollectionSettings.serialized");
   }

   /*
    * Converts a {@link Serializable} object into a byte array and stores it in
    * a file at given location.
    */
   private static void writeObject(Path path, Serializable s)
         throws IOException {

        try(ObjectOutputStream objectOutputStream =
                new ObjectOutputStream(Files.newOutputStream(path))) {
            objectOutputStream.writeObject(s);
        }
   }

   /**
    * Converts contents of a file back into an object.
    */
    private static <S> S readObject(Path path, Class<S> type) throws IOException,
         ClassNotFoundException {
        try(ObjectInputStream objectInputStream =
                new ObjectInputStream(Files.newInputStream(path))) {
            Object result = objectInputStream.readObject();
            return type.cast(result);
        }
   }

   /**
    * Process a single {@link TestFile} in a separate subprocess.
    * 
    * @param testName
    *           Name of the test used as prefix for test folder.
    */
   public static TestResult processTestFile(TestFile testFile,
            ProofCollectionSettings settings, Path pathToTempDir)
            throws Exception {
        return processTestFiles(Arrays.asList(testFile), settings,
                pathToTempDir).get(0);
   }

   /**
    * Process a list of {@link TestFile}s in a separate subprocess.
    * 
    * @param testName
    *           Name of the test used as prefix for test folder.
    */
   public static List<TestResult> processTestFiles(List<TestFile> testFiles,
            ProofCollectionSettings settings, Path pathToTempDir)
            throws Exception {

      writeObject(getLocationOfSerializedTestFiles(pathToTempDir),
                testFiles.toArray(new TestFile[testFiles.size()]));
      writeObject(
            getLocationOfSerializedProofCollectionSettings(pathToTempDir),
                settings);

      ProcessBuilder pb = new ProcessBuilder("java", "-classpath",
            System.getProperty("java.class.path"),
            ForkedTestFileRunner.class.getName(), pathToTempDir.toString());
      Process process = pb.inheritIO().start();
      process.waitFor();
      assertEquals("Executed process terminated with non-zero exit value.",
            process.exitValue(), 0);

      /*
       * Check if an exception occured and rethrow it if one occured.
       */
      Path exceptionFile = getLocationOfSerializedException(pathToTempDir);
      if (exceptionFile.toFile().exists()) {
            Throwable t = ForkedTestFileRunner.readObject(exceptionFile, Throwable.class);
         throw new Exception(
               "Subprocess returned exception (see cause for details):\n"
                     + t.getMessage(), t);
      }

      /*
       * Read serialized list of test results and return.
       */
      Path testResultsFile = getLocationOfSerializedTestResults(pathToTempDir);
      assertTrue("File containing serialized test results not present.",
            testResultsFile.toFile().exists());
        TestResult[] array = ForkedTestFileRunner.readObject(testResultsFile, TestResult[].class);

        return Arrays.asList(array);
   }

   public static void main(String[] args) throws IOException {
      /*
       * Check for existence of temp dir before entering try-catch block.
       * Throwables occuring in this block are written to temp dir, so its
       * existence needs to be confirmed beforehand.
       */
      Path tempDirectory = Paths.get(args[0]);
      if (!tempDirectory.toFile().exists()) {
         throw new Error("RunAllProofs temporary directory does not exist: "
               + tempDirectory);
      }

      try {
            TestFile[] testFiles =
                    ForkedTestFileRunner.readObject(
                            getLocationOfSerializedTestFiles(tempDirectory), TestFile[].class);
            ProofCollectionSettings settings =
                    ForkedTestFileRunner.
                    readObject(getLocationOfSerializedProofCollectionSettings(tempDirectory),
                            ProofCollectionSettings.class);
            installTimeoutWatchdog(settings, tempDirectory);
            Thread.sleep(4000);
         ArrayList<TestResult> testResults = new ArrayList<>();
         for (TestFile testFile : testFiles) {
            testResults.add(testFile.runKey(settings));
         }
         writeObject(getLocationOfSerializedTestResults(tempDirectory),
                    testResults.toArray(new TestResult[testResults.size()]));
        } catch (Throwable t) {
         writeObject(getLocationOfSerializedException(tempDirectory), t);
      }
   }

    /**
     * Launches a timeout-thread acting as a watchdog over this forked instance.
     *
     * If a time is specified in the settings, a fresh daemon thread is started
     * which terminates this instance after the specified time has elapsed.
     *
     * If no timeout has been specified, no thread is launched.
     *
     * @param settings
     *            the (non-null) settings to take the timeout from.
     * @param tempDirectory
     */
    private static void installTimeoutWatchdog(ProofCollectionSettings settings, final Path tempDirectory) {

        String timeoutString = settings.get(FORK_TIMEOUT_KEY);
        if(timeoutString == null) {
            return;
        }

        final boolean verbose = "true".equals(settings.get("verboseOutput"));

        final int timeout;
        try {
            timeout = Integer.parseInt(timeoutString);
        } catch(NumberFormatException ex) {
            throw new RuntimeException("The setting forkTimeout requires an integer, not " +
                        timeoutString, ex);
        }

        if(timeout <= 0) {
            throw new RuntimeException("The setting forkTimeout requires a positive integer, not " +
                    timeoutString);
        }

        Thread t = new Thread("Timeout watchdog") {
            public void run() {
                try {
                    if(verbose) {
                        System.err.println("Timeout watcher launched (" + timeout + " secs.)");
                    }
                    Thread.sleep(timeout * 1000);
                    InterruptedException ex =
                            new InterruptedException("forkTimeout (" + timeout + "sec.) elapsed");
                    writeObject(getLocationOfSerializedException(tempDirectory), ex);
                    // TODO consider something other than 0 here
                    if(verbose) {
                        System.err.println("Process timed out");
                    }
                    System.exit(0);
                } catch (Exception ex) {
                    System.err.println("The watchdog has been interrupted or failed. Timeout cancelled.");
                    ex.printStackTrace();
                }
            }
        };
        t.setDaemon(true);
        t.start();
    }

}
