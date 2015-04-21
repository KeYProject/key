package de.uka.ilkd.key.proof.runallproofs.proofcollection.settings;

import java.util.List;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.settings.ProofCollectionSettings.Entry;

/**
 * Factory class to create instances of type {@link ProofCollectionSettings}
 * 
 * @author Kai Wallisch
 *
 */
public class ProofCollectionSettingsFactory {
   public static ProofCollectionSettings createSettings(
         String proofCollectionFileLocaton, String globalKeYSettings,
         List<Entry> entries) {
      return new BaseProofCollectionSettings(proofCollectionFileLocaton,
            globalKeYSettings, entries);
   }

   public static ProofCollectionSettings createSettings(
         ProofCollectionSettings parentSettings, List<Entry> entries) {
      return new ExtendingProofCollectionSettings(parentSettings, entries);
   }
}
