package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.IOException;
import java.util.Arrays;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit;

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
         ProofCollectionSettings settings) throws IOException {

      String fileName = file.getKeYFile(settings).getName();

      return new RunAllProofsTestUnit(fileName, settings, getTempDirectory(fileName),
              Arrays.asList(file), true);
   }

}
