package de.uka.ilkd.key.proof.runallproofs;

import java.io.File;
import java.io.IOException;
import java.io.Serializable;
import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionSettings;

/**
 * A single unit that will be tested during {@link RunAllProofsTest} run.
 * 
 * @author Kai Wallisch
 */
public abstract class RunAllProofsTestUnit implements Serializable {

   /**
    * The name of this test.
    */
   public final String testCaseName;

   private final ProofCollectionSettings settings;

   /**
    * Method {@link Object#toString()} is used by class {@link RunAllProofsTest}
    * to determine the name of a test case. It is overridden here so that test
    * cases can be easily recognized by their name.
    */
   @Override
   public String toString() {
      return testCaseName;
   }

   public RunAllProofsTestUnit(String name, ProofCollectionSettings settings) {
      this.testCaseName = name;
      this.settings = settings;
   }

   /**
    * Run the test of this unit and return a {@link TestResult}.
    */
   public abstract TestResult runTest() throws Exception;

   /*
    * Temporary directory used by this test unit to store serialized data when
    * running in fork mode.
    */
   private Path tempDir = null;

   public Path getTempDir() throws IOException {
      File runAllProofsTempDir = settings.getTempDir();
      if (tempDir == null) {
         if (!runAllProofsTempDir.exists()) {
            runAllProofsTempDir.mkdirs();
         }
         tempDir = Files.createTempDirectory(runAllProofsTempDir.toPath(),
               testCaseName + "-");
      }
      return tempDir;
   }
}
