package de.uka.ilkd.key.proof.runallproofs;

import java.io.IOException;

/**
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class SingletonProofCollectionUnit extends ProofCollectionUnit {

   private final FileWithTestProperty file;

   public SingletonProofCollectionUnit(FileWithTestProperty fileWithTestProperty) {
      this.file = fileWithTestProperty;
   }

   @Override
   public boolean processProofObligations(ProofCollectionSettings settings) throws IOException {
      System.out.println(file.getFile(settings));
      System.out.println();
      return true;
   }

}
