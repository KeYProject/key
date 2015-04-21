package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.File;
import java.util.List;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionSettings.Entry;

/**
 * Factory class to create instances of type {@link ProofCollectionSettings}
 * 
 * @author Kai Wallisch
 *
 */
public class ProofCollectionSettingsFactory {

   /**
    * Creates a base {@link ProofCollectionSettings} object from the specified
    * parameters with no parent settings.
    */
   public static ProofCollectionSettings createSettings(
         String proofCollectionFileLocation, List<Entry> entries) {

      assert proofCollectionFileLocation != null : "No proof collection source file specified.";
      File sourceProofCollectionFile = new File(proofCollectionFileLocation)
            .getParentFile();
      assert sourceProofCollectionFile.isAbsolute() : "Expecting location of source proof collection "
            + "file to be given as absolute path.";
      assert sourceProofCollectionFile.exists() : "Given source proof collection file does not exist.";

      return new ProofCollectionSettings(sourceProofCollectionFile, entries);
   }

   /**
    * Creates a {@link ProofCollectionSettings} object that overrides an
    * existing {@link ProofCollectionSettings} object.
    */
   public static ProofCollectionSettings createSettings(
         final ProofCollectionSettings parentSettings, List<Entry> entries) {
      return new ProofCollectionSettings(
            parentSettings.sourceProofCollectionFile, entries) {

         @Override
         public String get(String key) {
            /*
             * First, try reading from local settings.
             */
            String ret = super.get(key);
            if (ret != null) {
               return ret;
            }
            else {
               /*
                * If no local settings value is available for the specified key,
                * return value of parent settings.
                */
               return parentSettings.get(key);
            }
         }

      };
   }
}
