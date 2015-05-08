package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.File;
import java.io.IOException;

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
 * and a {@link #path} String for the file location. Method
 * {@link #runKey(ProofCollectionSettings)} will verify {@link #testProperty}
 * for the given file.
 * 
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class TestFile extends ForkedTestFileRunner {

   final TestProperty testProperty;
   private final String path;

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
      this.path = pathToken.getText();
      this.testProperty = testProperty;
   }

   /**
    * Uses a {@link ProofCollectionSettings} object and the given {@link #path}
    * string to create a {@link File} object.
    * 
    * @param settings
    *           {@link ProofCollectionSettings} object that specifies the base
    *           directory that will be used in case {@link #path} specifies a
    *           relative path.
    * @return A {@link File} object that points to the target .key-file that
    *         will be tested.
    * @throws IOException
    *            Is thrown in case given .key-file is not a directory or does
    *            not exist.
    */
   public File getFile(ProofCollectionSettings settings) throws IOException {
      File baseDirectory = settings.getBaseDirectory();
      File keyFile = getAbsoluteFile(baseDirectory, path);

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
    * specified by {@link #path} string..
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
   public TestResult runKey(ProofCollectionSettings settings) throws Exception {
      try {
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
         finally {
            loadedProof.dispose();
         }

         return getRunAllProofsTestResult(success, settings);
      }
      catch (Throwable t) {
         throw new Exception(
               "Exception while attempting to prove file (see cause for details): "
                     + getFile(settings), t);
      }
   }

}
