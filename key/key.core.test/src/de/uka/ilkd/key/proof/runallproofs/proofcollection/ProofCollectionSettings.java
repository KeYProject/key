package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.File;
import java.io.Serializable;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Immutable settings type for proof collections. Use class
 * {@link ProofCollectionSettingsFactory} to get instances of this class.
 * 
 * @author Kai Wallisch
 *
 */
public class ProofCollectionSettings implements Serializable {

   /*
    * Constants for entries that may occur in field settingsMap.
    */
   public static final String BASE_DIRECTORY_KEY = "baseDirectory";
   public static final String KEY_SETTINGS_KEY = "keySettings";

   /**
    * File in which the present {@link ProofCollectionSettings} were declared.
    */
   public final File sourceProofCollectionFile;

   private final Map<String, String> settingsMap = new HashMap<>();

   /**
    * Non-public constructor. Use factory methods to create instances of this
    * class.
    * 
    * @param proofCollectionFileLocaton
    *           Location of the file in which the present settings were
    *           declared.
    */
   ProofCollectionSettings(File sourceProofCollectionFile, List<Entry> entries) {
      this.sourceProofCollectionFile = sourceProofCollectionFile;
      for (Entry entry : entries) {
         put(entry.key, entry.value);
      }
   }

   /**
    * Adds an entry to map {@link #settingsMap}. Objects of type
    * {@link ProofCollectionSettings} are designed to be immutable, so this
    * method has only private access.
    */
   private Object put(String key, String value) {
      if (settingsMap.containsKey(key)) {
         System.out.println("Warning: The key \"" + key
               + "\" is specified several times in file: "
               + sourceProofCollectionFile);
      }
      return settingsMap.put(key, value);
   }

   /**
    * Reads out generic settings, which were be specified as (key, value) pairs
    * during object creation.
    * 
    * @see Entry
    */
   public String get(String key) {
      return settingsMap.get(key);
   }

   /**
    * Returns KeY settings that will be used as default settings.
    */
   public String getGlobalKeYSettings() {
      return get(KEY_SETTINGS_KEY);
   }

   /**
    * Settings must specify a base directory. Relative paths can be treated as
    * relative to directory returned by this method.
    */
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
         return sourceProofCollectionFile;
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
            File ret = new File(sourceProofCollectionFile, baseDirectory);
            assert ret.isAbsolute() : "Computed File object is not absolute, which is not expected.";
            return ret;
         }
      }
   }

   /**
    * This class will be used for specifying settings entries as (key, value)
    * pairs.
    */
   public static class Entry {
      public final String key, value;

      public Entry(String key, String value) {
         this.key = key;
         this.value = value;
      }
   }

}
