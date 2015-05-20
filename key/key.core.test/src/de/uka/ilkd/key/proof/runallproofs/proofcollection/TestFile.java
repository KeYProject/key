package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.File;
import java.io.IOException;

import org.antlr.runtime.Token;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Statistics;
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
   private static File getAbsoluteFile(File baseDirectory, String pathName) {

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
    * {@link #pathToFile} string to create a {@link File} object that
    * (presumable) points to a KeY file. Settings are necessary for name
    * resolution of the file name.
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
   public File getKeYFile(ProofCollectionSettings settings) throws IOException {
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
            + getKeYFile(settings).toString();
      return new TestResult(message, success);
   }

   /**
    * Use KeY to verify that given {@link #testProperty} holds for KeY file that
    * is at file system location specified by {@link #pathToFile} string.
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
   public TestResult runKey(ProofCollectionSettings settings)
         throws Exception {

      // Initialize KeY settings.
      String gks = settings.getGlobalKeYSettings();
      ProofSettings.DEFAULT_SETTINGS.loadSettingsFromString(gks);

      // Name resolution for the available KeY file.
      File keyFile = getKeYFile(settings);

      // File that the created proof will be saved to.
      File proofFile = new File(keyFile.getAbsolutePath() + ".proof");

      KeYEnvironment<DefaultUserInterfaceControl> env = null;
      Proof loadedProof = null;
      boolean success;
      try {
         // Initialize KeY environment and load proof.
         env = KeYEnvironment.load(keyFile, null, null, null);
         loadedProof = env.getLoadedProof();

         // For a reload test we are done at this point. Loading was successful.
         if (testProperty == TestProperty.LOADABLE) {
            return getRunAllProofsTestResult(true, settings);
         }

         // Run KeY prover.
         env.getProofControl().startAndWaitForAutoMode(loadedProof);
         success = (testProperty == TestProperty.PROVABLE) == loadedProof
               .closed();

         // Write statistics.
         File statisticsFile = settings.getStatisticsFile();
         if (statisticsFile != null) {
            Statistics.appendStatisticsToFile(statisticsFile, loadedProof,
                  false, keyFile);
         }

         /*
          * Reload available proof if it was tested whether available KeY file
          * is provable and the previous proof attempt was successful.
          */
         /*
         if ((testProperty == TestProperty.PROVABLE) && success) {
            // Save the available proof to a temporary file.
            loadedProof.saveToFile(proofFile);
            reloadProof(proofFile);
         }
         */
      }
      catch (Throwable t) {
         throw new Exception(
               "Exception while attempting to prove file (see cause for details): "
                     + keyFile, t);
      }
      finally {
         if (loadedProof != null) {
            loadedProof.dispose();
         }
         if (env != null) {
            env.dispose();
         }
      }

      return getRunAllProofsTestResult(success, settings);
   }

   /**
    * 
    * Reload proof that was previously saved at the location corresponding to
    * the given {@link File} object.
    * 
    * @param proofFile
    *           File that contains the proof that will be (re-)loaded.
    */
   private void reloadProof(File proofFile) throws Exception {
      /*
       * Reload proof and dispose corresponding KeY environment immediately
       * afterwards. If no exception is thrown it is assumed that loading works
       * properly.
       */
      KeYEnvironment<DefaultUserInterfaceControl> proofLoadEnvironment = null;
      Proof savedProof = null;
      try {
         proofLoadEnvironment = KeYEnvironment
               .load(proofFile, null, null, null);
         savedProof = proofLoadEnvironment.getLoadedProof();
      }
      catch (Throwable t) {
         throw new Exception(
               "Exception while loading proof (see cause for details): "
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
   }

}
