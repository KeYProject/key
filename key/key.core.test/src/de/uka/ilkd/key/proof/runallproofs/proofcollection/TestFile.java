package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.File;
import java.io.IOException;
import java.io.Serializable;

import org.antlr.runtime.Token;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit.TestResult;
import de.uka.ilkd.key.settings.ProofSettings;

/**
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class TestFile implements Serializable {

   final TestProperty testProperty;
   private final String path;

   /**
    * In order to ensure that the implementation is independent of working
    * directory, this method can be used to return an absolute {@link File}
    * object.
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

   public TestResult runKey(ProofCollectionSettings settings)
         throws Exception {
      try {
         String gks = settings.getGlobalKeYSettings();
         ProofSettings.DEFAULT_SETTINGS.loadSettingsFromString(gks);

         KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(getFile(settings),
               null, null, null);
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
