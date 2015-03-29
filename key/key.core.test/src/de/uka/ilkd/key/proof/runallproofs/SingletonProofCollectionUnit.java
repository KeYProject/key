package de.uka.ilkd.key.proof.runallproofs;

//import de.uka.ilkd.key.ui.ConsoleUserInterfaceControl;

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
   public boolean processProofObligations() {
      return true;
   }

}
