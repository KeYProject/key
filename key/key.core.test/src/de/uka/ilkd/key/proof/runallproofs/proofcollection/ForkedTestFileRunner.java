package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import static de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest.KEY_CORE_TEST;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertEquals;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
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

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit;
import de.uka.ilkd.key.proof.runallproofs.TestResult;

/**
 * Executes KeY on a list of {@link TestFile}s in a separate process.
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

   private static void writeObject(Path path, Serializable s)
         throws IOException {
      Files.write(path, convertToByteArray(s));
   }

   @SuppressWarnings("unchecked")
   private static <G> G readObject(Path path) throws IOException,
         ClassNotFoundException {
      return (G) convertToObject(Files.readAllBytes(path));
   }

   /**
    * This method is used to convert a {@link Serializable} object into a byte
    * array.
    */
   private static byte[] convertToByteArray(Serializable o) throws IOException {
      ByteArrayOutputStream byteArrayOutputStream = new ByteArrayOutputStream();
      ObjectOutputStream objectOutputStream = new ObjectOutputStream(
            byteArrayOutputStream);
      objectOutputStream.writeObject(o);
      objectOutputStream.flush();
      return byteArrayOutputStream.toByteArray();
   }

   /**
    * This method is used to convert a byte array back into a
    * {@link Serializable}
    */
   private static Object convertToObject(byte[] bytes) throws IOException,
         ClassNotFoundException {
      ByteArrayInputStream byteArrayInputStream = new ByteArrayInputStream(
            bytes);
      ObjectInputStream objectInputStream = new ObjectInputStream(
            byteArrayInputStream);
      return objectInputStream.readObject();
   }

   public static TestResult processTestFile(TestFile testFile,
         ProofCollectionSettings settings) throws Exception {
      /*
       * Passing argument testFile and using null as temp directory prefix. null
       * as temp directory prefix causes Java to create a temporary directory
       * with random name.
       */
      return processTestFile(testFile, settings, null);
   }

   public static TestResult processTestFile(TestFile testFile,
         ProofCollectionSettings settings, String tempDirectoryPrefix)
         throws Exception {
      return processTestFiles(Arrays.asList(testFile), settings,
            tempDirectoryPrefix).get(0);
   }

   /**
    * Runs the {@link RunAllProofsTestUnit} belonging to a
    * {@link RunAllProofsTest} object in a separate process.
    */
   public static List<TestResult> processTestFiles(List<TestFile> testFiles,
         ProofCollectionSettings settings, String tempDirectoryPrefix)
         throws Exception {
      File runAllProofsFolder = new File(KEY_CORE_TEST, "testresults"
            + File.separator + "runallproofs");
      if (!runAllProofsFolder.exists()) {
         System.out.println("Creating directory for temporary files: "
               + runAllProofsFolder);
         Files.createDirectories(runAllProofsFolder.toPath());
      }

      Path tempDirectory = Files.createTempDirectory(
            runAllProofsFolder.toPath(), tempDirectoryPrefix);

      writeObject(getLocationOfSerializedTestFiles(tempDirectory),
            (Serializable) testFiles);
      writeObject(
            getLocationOfSerializedProofCollectionSettings(tempDirectory),
            (Serializable) settings);

      ProcessBuilder pb = new ProcessBuilder("java", "-classpath",
            System.getProperty("java.class.path"),
            ForkedTestFileRunner.class.getName(), tempDirectory.toString());
      Process process = pb.inheritIO().start();
      process.waitFor();
      assertEquals("Executed process terminated with non-zero exit value.",
            process.exitValue(), 0);

      /*
       * Check if an exception occured and rethrow it if one occured.
       */
      Path exceptionFile = getLocationOfSerializedException(tempDirectory);
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
      Path testResultsFile = getLocationOfSerializedTestResults(tempDirectory);
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
