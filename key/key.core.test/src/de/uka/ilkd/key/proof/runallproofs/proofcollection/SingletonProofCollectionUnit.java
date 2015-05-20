package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.IOException;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit;
import de.uka.ilkd.key.proof.runallproofs.TestResult;

/**
 * A {@link ProofCollectionUnit} that is created from a single {@link TestFile}
 * that is not declared as part of a group.
 * 
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class SingletonProofCollectionUnit extends ProofCollectionUnit {

   private final TestFile file;

   public SingletonProofCollectionUnit(TestFile fileWithTestProperty) {
      this.file = fileWithTestProperty;
   }

   @Override
   public RunAllProofsTestUnit createRunAllProofsTestUnit(
         final ProofCollectionSettings settings) throws IOException {
      final String fileName = file.getKeYFile(settings).getName();
      return new RunAllProofsTestUnit(fileName) {

         @Override
         public TestResult runTest() throws Exception {
            ForkMode forkMode = settings.getForkMode();
            if (forkMode == ForkMode.NOFORK) {
               return file.runKey(settings);
            }
            else if (forkMode == ForkMode.PERGROUP
                  || forkMode == ForkMode.PERFILE) {
               return ForkedTestFileRunner.processTestFile(file, settings,
                     getTempDirectory(fileName));
            }
            else {
               throw new RuntimeException("Unexpected value for fork mode: "
                     + forkMode);
            }
         }

      };
   }

}
