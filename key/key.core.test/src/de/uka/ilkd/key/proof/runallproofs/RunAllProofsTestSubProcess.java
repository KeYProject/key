package de.uka.ilkd.key.proof.runallproofs;

import static de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest.KEY_CORE_TEST;
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

/**
 * {@link #main(String[])} method of this class will be executed in a separate
 * thread in case RunAllProofsTest is configured to run each
 * {@link RunAllProofsTestUnit} in a separate process. Method
 * {@link #executeRunAllProofsTestSubProcess(RunAllProofsTest)} does the process
 * creation work (and related tasks).
 * 
 * @author Kai Wallisch
 *
 */
public class RunAllProofsTestSubProcess {

   private static Path getLocationOfSerializedRunAllProofsTest(
         Path tempDirectory) {
      return Paths.get(tempDirectory.toString(), "RunAllProofsTest.serialized");
   }

   private static Path getLocationOfSerializedException(Path tempDirectory) {
      return Paths.get(tempDirectory.toString(), "Exception.serialized");
   }

   private static Path getLocationOfSerializedMessage(Path tempDirectory) {
      return Paths.get(tempDirectory.toString(), "Message.serialized");
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

   /**
    * Runs the {@link RunAllProofsTestUnit} belonging to a
    * {@link RunAllProofsTest} object in a separate process.
    */
   public static void executeRunAllProofsTestSubProcess(
         RunAllProofsTest runAllProofsTest) throws Exception {
      File runAllProofsFolder = new File(KEY_CORE_TEST, "testresults"
            + File.separator + "runallproofs");
      if (!runAllProofsFolder.exists()) {
         System.out.println("Creating directory for temporary files: "
               + runAllProofsFolder);
         Files.createDirectories(runAllProofsFolder.toPath());
      }

      Path tempDirectory = Files.createTempDirectory(
            runAllProofsFolder.toPath(),
            runAllProofsTest.unit.getTempDirectoryPrefix());

      Files.write(getLocationOfSerializedRunAllProofsTest(tempDirectory),
            convertToByteArray(new Object[] { runAllProofsTest }));
      ProcessBuilder pb = new ProcessBuilder("java", "-classpath",
            System.getProperty("java.class.path"),
            RunAllProofsTestSubProcess.class.getName(),
            tempDirectory.toString());
      Process process = pb.inheritIO().start();
      process.waitFor();
      assertEquals("Executed process terminated with non-zero exit value.",
            process.exitValue(), 0);

      Path messageFile = getLocationOfSerializedMessage(tempDirectory);
      if (messageFile.toFile().exists()) {
         System.out.println((String) convertToObject(Files
               .readAllBytes(messageFile)));
      }

      Path exceptionFile = getLocationOfSerializedException(tempDirectory);
      if (exceptionFile.toFile().exists()) {
         Throwable t = (Throwable) convertToObject(Files
               .readAllBytes(exceptionFile));
         throw new Exception(
               "Subprocess returned exception (see cause for details):\n"
                     + t.getMessage(), t);
      }
   }

   public static void main(String[] args) throws IOException {
      Path tempDirectory = Paths.get(args[0]);
      if (!tempDirectory.toFile().exists()) {
         throw new Error("Temporary directory does not exist: " + tempDirectory);
      }

      try {
         RunAllProofsTest runAllProofsTest = (RunAllProofsTest) convertToObject(Files
               .readAllBytes(getLocationOfSerializedRunAllProofsTest(tempDirectory)));
         SuccessReport report = runAllProofsTest.unit.runTest();
         Files.write(getLocationOfSerializedMessage(tempDirectory),
               convertToByteArray(report.message));
      }
      catch (Throwable t) {
         Files.write(getLocationOfSerializedException(tempDirectory),
               convertToByteArray(t));
      }
   }

}
