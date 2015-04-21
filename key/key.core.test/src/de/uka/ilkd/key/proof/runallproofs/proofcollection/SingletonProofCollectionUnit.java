package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit;
import de.uka.ilkd.key.proof.runallproofs.SuccessReport;

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
         final ProofCollectionSettings settings) {
      return new RunAllProofsTestUnit() {

         @Override
         public SuccessReport runTest() throws Exception {
            return file.runKey(settings);
         }

      };
   }

}
