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

public class ProofCollectionSubProcess {

   private static Path getArgumentPath(Path tempDirectory) {
      return Paths.get(tempDirectory.toString(), "args.bin");
   }

   private static Path getExceptionPath(Path tempDirectory) {
      return Paths.get(tempDirectory.toString(), "exception.bin");
   }

   private static Path getMessagePath(Path tempDirectory) {
      return Paths.get(tempDirectory.toString(), "message.txt");
   }

   public static void main(String[] args) throws IOException {
      Path tempDirectory = Paths.get(args[0]);
      if (!tempDirectory.toFile().exists()) {
         throw new Error("Temporary directory does not exist: " + tempDirectory);
      }

      try {
         Object[] tmp = (Object[]) convertToObject(Files
               .readAllBytes(getArgumentPath(tempDirectory)));
         ProofCollectionSettings settings = (ProofCollectionSettings) tmp[0];
         ProofCollectionUnit unit = (ProofCollectionUnit) tmp[1];
         SuccessReport report = unit.processProofObligations(settings);
         Files.write(getMessagePath(tempDirectory),
               convertToByteArray(report.message));
      }
      catch (Throwable t) {
         Files.write(getExceptionPath(tempDirectory), convertToByteArray(t));
      }
   }

   private static Object convertToObject(byte[] bytes) throws IOException,
         ClassNotFoundException {
      ByteArrayInputStream byteArrayInputStream = new ByteArrayInputStream(
            bytes);
      ObjectInputStream objectInputStream = new ObjectInputStream(
            byteArrayInputStream);
      return objectInputStream.readObject();
   }

   private static byte[] convertToByteArray(Serializable o) throws IOException {
      ByteArrayOutputStream byteArrayOutputStream = new ByteArrayOutputStream();
      ObjectOutputStream objectOutputStream = new ObjectOutputStream(
            byteArrayOutputStream);
      objectOutputStream.writeObject(o);
      objectOutputStream.flush();
      return byteArrayOutputStream.toByteArray();
   }

   public static void executeRunAllProofsTest(RunAllProofsTest runAllProofsTest)
         throws Exception {
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

      Files.write(getArgumentPath(tempDirectory),
            convertToByteArray(new Object[] { runAllProofsTest.settings,
                  runAllProofsTest.unit }));
      ProcessBuilder pb = new ProcessBuilder("java", "-classpath",
            System.getProperty("java.class.path"),
            ProofCollectionSubProcess.class.getName(), tempDirectory.toString());
      // System.out.println("Starting process: " + pb.command());
      Process process = pb.inheritIO().start();
      process.waitFor();
      assertEquals("Executed process terminated with non-zero exit value.",
            process.exitValue(), 0);

      Path messageFile = getMessagePath(tempDirectory);
      if (messageFile.toFile().exists()) {
         System.out.println((String) convertToObject(Files
               .readAllBytes(messageFile)));
      }

      Path exceptionFile = getExceptionPath(tempDirectory);
      if (exceptionFile.toFile().exists()) {
         Throwable t = (Throwable) convertToObject(Files
               .readAllBytes(exceptionFile));
         throw new Exception(
               "Subprocess returned exception (see cause for details):\n"
                     + t.getMessage(), t);
      }
   }

}
