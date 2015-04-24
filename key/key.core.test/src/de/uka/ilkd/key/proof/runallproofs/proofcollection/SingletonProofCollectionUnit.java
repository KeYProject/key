package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.IOException;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit;

/**
 * A {@link ProofCollectionUnit} that is created from a separate
 * {@link TestFile} that is not declared as part of a group.
 * 
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class SingletonProofCollectionUnit implements ProofCollectionUnit {

   private final TestFile file;

   public SingletonProofCollectionUnit(TestFile fileWithTestProperty) {
      this.file = fileWithTestProperty;
   }

   @Override
   public RunAllProofsTestUnit createRunAllProofsTestUnit(
         final ProofCollectionSettings settings) throws IOException {
      return new RunAllProofsTestUnit(file.getFile(settings).getName()) {

         @Override
         public TestResult runTest() throws Exception {
            return file.runKey(settings);
         }

      };
   }

}
