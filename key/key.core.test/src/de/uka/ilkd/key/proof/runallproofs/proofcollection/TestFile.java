package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import org.antlr.runtime.Token;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest;
import de.uka.ilkd.key.proof.runallproofs.TestResult;
import de.uka.ilkd.key.settings.ProofSettings;

/**
 * Data structure for .key-files that will be tested during
 * {@link RunAllProofsTest} execution. It consists of a {@link #testProperty}
 * and a {@link #pathToFile} String for the file location. Method
 * {@link #runKey(ProofCollectionSettings)} will verify {@link #testProperty}
 * for the given file.
 * 
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class TestFile extends ForkedTestFileRunner {

   final TestProperty testProperty;
   private final String pathToFile;

   /**
    * In order to ensure that the implementation is independent of working
    * directory, this method can be used to return an absolute {@link File}
    * object.
    * 
    * @param baseDirectory
    *           Base directory that will be used as start location in case given
    *           path name is a relative path.
    * @param pathName
    *           Path whose associated {@link File} object will be returned.
    * @return {@link File} object pointing to given path name relative to given
    *         base directory.
    */
   public static File getAbsoluteFile(File baseDirectory, String pathName) {

      /*
       * Caller of this method must provide an absolute path as initial
       * directory.
       */
      if (!baseDirectory.isAbsolute()) {
         throw new RuntimeException("Expecting an absolute path but found: "
               + baseDirectory);
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

   public TestFile(TestProperty testProperty, Token pathToken) {
      this.pathToFile = pathToken.getText();
      this.testProperty = testProperty;
   }

   /**
    * Uses a {@link ProofCollectionSettings} object and the given
    * {@link #pathToFile} string to create a {@link File} object.
    * 
    * @param settings
    *           {@link ProofCollectionSettings} object that specifies the base
    *           directory that will be used in case {@link #pathToFile}
    *           specifies a relative path.
    * @return A {@link File} object that points to the target .key-file that
    *         will be tested.
    * @throws IOException
    *            Is thrown in case given .key-file is not a directory or does
    *            not exist.
    */
   public File getFile(ProofCollectionSettings settings) throws IOException {
      File baseDirectory = settings.getBaseDirectory();
      File keyFile = getAbsoluteFile(baseDirectory, pathToFile);

      if (keyFile.isDirectory()) {
         String exceptionMessage = "Expecting a file, but found a directory: "
               + keyFile.getAbsolutePath();
         throw new IOException(exceptionMessage);
      }

      if (!keyFile.exists()) {
         String exceptionMessage = "The given file does not exist: "
               + keyFile.getAbsolutePath();
         throw new IOException(exceptionMessage);
      }
      return keyFile;
   }

   private TestResult getRunAllProofsTestResult(boolean success,
         ProofCollectionSettings settings) throws IOException {
      String message = (success ? "pass: " : "FAIL: ")
            + "Verifying property \"" + testProperty.toString().toLowerCase()
            + "\"" + (success ? " was successful " : " failed ") + "for file: "
            + getFile(settings).toString();
      return new TestResult(message, success);
   }

   /**
    * Use given to verify that {@link #testProperty} holds for given .key-file
    * specified by {@link #pathToFile} string..
    * 
    * @param settings
    *           {@link ProofCollectionSettings} object that specifies settings
    *           which will be used for the test run.
    * @return Returns a {@link TestResult} object, which consists of a boolean
    *         value indicating whether test run was successful and a message
    *         string that can be printed out on command line to inform the user
    *         about the test result.
    * @throws Exception
    *            Any exception that may occur during KeY execution will be
    *            converted into an {@link Exception} object with original
    *            exception as cause.
    */
   public TestResult runKey(ProofCollectionSettings settings, Path pathToTempDir)
         throws Exception {
      String gks = settings.getGlobalKeYSettings();
      ProofSettings.DEFAULT_SETTINGS.loadSettingsFromString(gks);

      KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(
            getFile(settings), null, null, null);
      Proof loadedProof = env.getLoadedProof();

      if (testProperty == TestProperty.LOADABLE) {
         loadedProof.dispose();
         getRunAllProofsTestResult(true, settings);
      }

      boolean success;
      try {
         env.getProofControl().startAndWaitForAutoMode(loadedProof);
         success = (testProperty == TestProperty.PROVABLE) == loadedProof
               .closed();
      }
      catch (Throwable t) {
         loadedProof.dispose();
         throw new Exception(
               "Exception while attempting to prove file (see cause for details): "
                     + getFile(settings), t);
      }

      /*
       * Save and reload proof.
       */
      File proofFile = new File(pathToTempDir.toFile(), getFile(settings)
            .getName() + ".proof");
      KeYEnvironment<DefaultUserInterfaceControl> proofLoadEnvironment = null;
      Proof savedProof = null;
      try {
         /*
          * Save the proof to a temporary file.
          */
         loadedProof.saveToFile(proofFile);

         /*
          * Reload proof and dispose corresponding KeY environment immediately
          * afterwards. If no exceptions are thrown we assume loading works
          * fine.
          */
         proofLoadEnvironment = KeYEnvironment
               .load(proofFile, null, null, null);
         savedProof = proofLoadEnvironment.getLoadedProof();
      }
      catch (Throwable t) {
         loadedProof.dispose();
         throw new Exception(
               "Exception while saving/loading proof (see cause for details): "
                     + proofFile, t);
      }
      finally {
         if (savedProof != null) {
            savedProof.dispose();
         }
         if (proofLoadEnvironment != null) {
            proofLoadEnvironment.dispose();
         }
      }

      /*
       * Write statistics.
       */
      File statisticsFile = new File(pathToTempDir.toFile(), getFile(settings)
            .getName() + ".statistics");
      Files.write(statisticsFile.toPath(), loadedProof.statistics().toString()
            .getBytes());
      loadedProof.dispose();

      return getRunAllProofsTestResult(success, settings);

   }

}
