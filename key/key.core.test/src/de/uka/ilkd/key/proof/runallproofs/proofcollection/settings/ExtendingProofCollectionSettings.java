package de.uka.ilkd.key.proof.runallproofs.proofcollection.settings;

import java.io.File;
import java.util.List;

/**
 * {@link ProofCollectionSettings} implementation that overrides an existing
 * {@link ProofCollectionSettings} object.
 */
class ExtendingProofCollectionSettings extends AbstractProofCollectionSettings {

   private final ProofCollectionSettings parentSettings;

   ExtendingProofCollectionSettings(ProofCollectionSettings parentSettings,
         List<Entry> entries) {
      super(parentSettings.getGlobalKeYSettings(), entries);
      this.parentSettings = parentSettings;
   }

   @Override
   public String get(String key) {
      /*
       * First, try to read out local settings.
       */
      String ret = super.get(key);
      if (ret != null) {
         return ret;
      }
      else {
         /*
          * If no local settings value is available for specified key, return
          * value of parent settings (may be null as well).
          */
         return parentSettings.get(key);
      }
   }

   @Override
   public File getSourceProofCollectionFile() {
      /*
       * Parent settings and local settings should belong to the same proof
       * collection source file. For that reason, we can return value of parent
       * settings here.
       */
      return parentSettings.getSourceProofCollectionFile();
   }

}
