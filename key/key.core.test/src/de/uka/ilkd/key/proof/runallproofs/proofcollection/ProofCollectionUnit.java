package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.IOException;
import java.io.Serializable;
import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit;

/**
 * Parser {@link ProofCollectionParser} splits a file into several
 * {@link ProofCollectionUnit}s during parsing. The only constraint on objects
 * of this type is that a {@link RunAllProofsTestUnit} can be created from them.
 * See implementations {@link GroupedProofCollectionUnit} and
 * {@link SingletonProofCollectionUnit} for further details.
 * 
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public abstract class ProofCollectionUnit implements Serializable {

   public static Path getRunAllProofsTempDirectory(String name)
         throws IOException {
      if (!RunAllProofsTest.RUNALLPROOFS_TMP_FOLDER.exists()) {
         RunAllProofsTest.RUNALLPROOFS_TMP_FOLDER.mkdirs();
      }
      return Files.createTempDirectory(RunAllProofsTest.RUNALLPROOFS_TMP_FOLDER.toPath(),
            name + "-");
   }

   /**
    * 
    * Creates a {@link RunAllProofsTestUnit} from this
    * {@link ProofCollectionUnit}.
    * 
    * @param parentSettings
    *           Settings used during execution of returned
    *           {@link RunAllProofsTestUnit}.
    */
   public abstract RunAllProofsTestUnit createRunAllProofsTestUnit(
         ProofCollectionSettings parentSettings) throws IOException;
}
