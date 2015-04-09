package de.uka.ilkd.key.proof.runallproofs;

import java.io.File;
import java.io.IOException;
import java.io.Serializable;

import org.antlr.runtime.Token;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

/**
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class FileWithTestProperty implements Serializable {

   final TestProperty testProperty;
   private final String path;
   private File keyFile = null;

   /**
    * In order to ensure that the implementation is independent of working
    * directory, this method can be used to return an absolute {@link File}
    * object.
    */
   public static File getAbsoluteFile(File initialDirectory, String pathName) {

      /*
       * Caller of this method must provide an absolute path as initial
       * directory.
       */
      if (!initialDirectory.isAbsolute()) {
         throw new RuntimeException("Expecting an absolute path but found: "
               + initialDirectory);
      }

      /*
       * Initial directory is ignored in case provided path name is absolute.
       */
      File tmp = new File(pathName);
      File ret = tmp.isAbsolute() ? tmp : new File(initialDirectory, pathName);

      /*
       * Resulting file object should be absolute. This is just a safety check.
       */
      assert ret.isAbsolute() : "Expecting an absolute path but found: " + ret;

      return ret;
   }

   public FileWithTestProperty(TestProperty testProperty, Token pathToken) {
      this.path = pathToken.getText();
      this.testProperty = testProperty;
   }

   public File getFile(ProofCollectionSettings settings) throws IOException {
      File initialDirectory = settings.initialDirectory;

      if (keyFile == null) {
         keyFile = getAbsoluteFile(initialDirectory, path);
      }

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

   public SuccessReport verifyTestProperty(ProofCollectionSettings settings)
         throws ProblemLoaderException, IOException {
      KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(
            new JavaProfile(), getFile(settings), null, null, false);
      Proof loadedProof = env.getLoadedProof();

      if (testProperty == TestProperty.LOADABLE) {
         return new SuccessReport("success "
               + testProperty.toString().toLowerCase() + " "
               + getFile(settings), true);
      }

      env.getProofControl().startAndWaitForAutoMode(loadedProof);
      boolean success = (testProperty == TestProperty.PROVABLE) == loadedProof
            .closed();
      loadedProof.dispose();

      return new SuccessReport((success ? "success " : "FAILED ")
            + testProperty.toString().toLowerCase() + " " + getFile(settings),
            success);
   }

}
