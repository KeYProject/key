package de.uka.ilkd.key.proof.runallproofs.proofcollection.settings;

import java.io.File;
import java.util.List;

/**
 * {@link ProofCollectionSettings} implementation that does not override an
 * existing {@link ProofCollectionSettings} object.
 */
class BaseProofCollectionSettings extends AbstractProofCollectionSettings {

   private final File sourceProofCollectionFile;

   BaseProofCollectionSettings(String proofCollectionFileLocaton,
         String globalKeYSettings, List<Entry> entries) {
      super(globalKeYSettings, entries);

      assert proofCollectionFileLocaton != null : "No proof collection source file specified.";
      sourceProofCollectionFile = new File(proofCollectionFileLocaton)
            .getParentFile();
      assert sourceProofCollectionFile.isAbsolute() : "Expecting location of source proof collection "
            + "file to be given as absolute path.";
      assert sourceProofCollectionFile.exists() : "Given source proof collection file does not exist.";
   }

   @Override
   public File getSourceProofCollectionFile() {
      return sourceProofCollectionFile;
   }

}
