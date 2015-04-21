package de.uka.ilkd.key.proof.runallproofs.proofcollection.settings;

import java.io.File;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Abstract implementation of {@link ProofCollectionSettings}. This
 * implementation does not implement the method
 * {@link ProofCollectionSettings#getSourceProofCollectionFile()}.
 */
abstract class AbstractProofCollectionSettings implements
      ProofCollectionSettings {

   private final Map<String, String> settingsMap = new HashMap<>();
   private final String globalKeYSettings;

   AbstractProofCollectionSettings(String globalKeYSettings, List<Entry> entries) {
      for (Entry entry : entries) {
         put(entry.key, entry.value);
      }
      this.globalKeYSettings = globalKeYSettings;
   }

   private Object put(String key, String value) {
      if (settingsMap.containsKey(key)) {
         System.out
               .println("Warning, key written twice in proof collection settings: "
                     + key);
         System.out.println("Check file " + getSourceProofCollectionFile()
               + " for duplicate settings entries.");
      }
      return settingsMap.put(key, value);
   }

   @Override
   public String get(String key) {
      return settingsMap.get(key);
   }

   @Override
   public String getGlobalKeYSettings() {
      return globalKeYSettings;
   }

   @Override
   public File getBaseDirectory() {
      /*
       * Get base directory as specified in the settings.
       */
      String baseDirectory = get(BASE_DIRECTORY_KEY);

      if (baseDirectory == null) {
         /*
          * In case no base directory is specified, return location of source
          * file.
          */
         return getSourceProofCollectionFile();
      }
      else {
         File baseDirectoryFile = new File(baseDirectory);
         if (baseDirectoryFile.isAbsolute()) {
            /*
             * In case specified base directory is given as absolute location,
             * it will be returned without modification.
             */
            return baseDirectoryFile;
         }
         else {
            /*
             * In case specified base directory is given as relative location,
             * it will be treated as relative to source file location.
             */
            File ret = new File(getSourceProofCollectionFile(), baseDirectory);
            assert ret.isAbsolute() : "Computed File object is not absolute, which is not expected.";
            return ret;
         }
      }
   }

}
