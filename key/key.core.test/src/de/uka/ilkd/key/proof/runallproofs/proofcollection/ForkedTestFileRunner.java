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
      /*
       * Convert given object into a byte array.
       */
      ByteArrayOutputStream byteArrayOutputStream = new ByteArrayOutputStream();
      ObjectOutputStream objectOutputStream = new ObjectOutputStream(
            byteArrayOutputStream);
      objectOutputStream.writeObject(s);
      objectOutputStream.flush();
      byte[] bytes = byteArrayOutputStream.toByteArray();

      /*
       * Write byte array to a file.
       */
      Files.write(path, bytes);
   }

   /**
    * Converts contents of a file back into an object.
    */
   @SuppressWarnings("unchecked")
   private static <S> S readObject(Path path) throws IOException,
         ClassNotFoundException {
      /*
       * Convert content of given path (which points to a file) into a byte
       * array.
       */
      byte[] bytes = Files.readAllBytes(path);

      /*
       * Convert byte array back into an object.
       */
      ByteArrayInputStream byteArrayInputStream = new ByteArrayInputStream(
            bytes);
      ObjectInputStream objectInputStream = new ObjectInputStream(
            byteArrayInputStream);
      return (S) objectInputStream.readObject();
   }

   /**
    * Process a single {@link TestFile} in a separate subprocess.
    * 
    * @param testName
    *           Name of the test used as prefix for test folder.
    */
   public static TestResult processTestFile(TestFile testFile,
         ProofCollectionSettings settings, Path pathToTempDir) throws Exception {
      return processTestFiles(Arrays.asList(testFile), settings, pathToTempDir)
            .get(0);
   }

   /**
    * Process a list of {@link TestFile}s in a separate subprocess.
    * 
    * @param testName
    *           Name of the test used as prefix for test folder.
    */
   public static List<TestResult> processTestFiles(List<TestFile> testFiles,
         ProofCollectionSettings settings, Path pathToTempDir) throws Exception {

      writeObject(getLocationOfSerializedTestFiles(pathToTempDir),
            (Serializable) testFiles);
      writeObject(
            getLocationOfSerializedProofCollectionSettings(pathToTempDir),
            (Serializable) settings);

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
         Throwable t = ForkedTestFileRunner
               .<Throwable> readObject((exceptionFile));
         throw new Exception(
               "Subprocess returned exception (see cause for details):\n"
                     + t.getMessage(), t);
      }

      /*
       * Read serialized list of test results and return.
       */
      Path testResultsFile = getLocationOfSerializedTestResults(pathToTempDir);
      assertTrue("File containing serialized test results not presend.",
            testResultsFile.toFile().exists());
      return ForkedTestFileRunner
            .<List<TestResult>> readObject((testResultsFile));
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
         List<TestFile> testFiles = ForkedTestFileRunner
               .<List<TestFile>> readObject(getLocationOfSerializedTestFiles(tempDirectory));
         ProofCollectionSettings settings = ForkedTestFileRunner
               .<ProofCollectionSettings> readObject(getLocationOfSerializedProofCollectionSettings(tempDirectory));

         ArrayList<TestResult> testResults = new ArrayList<>();
         for (TestFile testFile : testFiles) {
            testResults.add(testFile.runKey(settings));
         }
         writeObject(getLocationOfSerializedTestResults(tempDirectory),
               testResults);
      }
      catch (Throwable t) {
         writeObject(getLocationOfSerializedException(tempDirectory), t);
      }
   }

}
