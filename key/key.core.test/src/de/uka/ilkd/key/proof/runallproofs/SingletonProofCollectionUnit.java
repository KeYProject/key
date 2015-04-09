package de.uka.ilkd.key.proof.runallproofs;


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
   public SuccessReport processProofObligations(ProofCollectionSettings settings)
         throws Exception {
      return file.verifyTestProperty(settings);
   }

}
