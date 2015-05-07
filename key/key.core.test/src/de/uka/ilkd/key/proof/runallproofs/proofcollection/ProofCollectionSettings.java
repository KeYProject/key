package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.File;
import java.io.Serializable;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest;
import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * Immutable settings type for proof collections. Specifies settings used during
 * test run of {@link RunAllProofsTest}.
 * 
 * @author Kai Wallisch
 *
 */
public class ProofCollectionSettings implements Serializable {

   /*
    * Known constants for entries that may occur in field settingsMap.
    */
   private static final String BASE_DIRECTORY_KEY = "baseDirectory";
   private static final String KEY_SETTINGS_KEY = "keySettings";
   private static final String FORK_MODE = "forkMode";

   public enum ForkMode {
      PERFILE, PERGROUP, NOFORK
   }

   /**
    * {@link List} of default entries that will be available in every
    * {@link ProofCollectionSettings} object.
    */
   private static final List<Entry> DEFAULT_ENTRIES;
   static {
      /*
       * Iterating over all system properties to get default entries. System
       * properties starting with "key.runallproofs." are relevant for proof
       * collection settings.
       */
      List<Entry> tmp = new LinkedList<>();
      Set<Map.Entry<Object, Object>> entrySet = System.getProperties()
            .entrySet();
      for (Map.Entry<Object, Object> entry : entrySet) {
         String key = (String) entry.getKey();
         String value = (String) entry.getValue();
         if (key.startsWith("key.runallproofs.")) {
            key = key.substring(17);// strip "key.runallproofs." from key
            tmp.add(new Entry(key, value));
         }
      }
      DEFAULT_ENTRIES = Collections.unmodifiableList(tmp);
   }

   /**
    * Converts a list of map entries to an unmodifiable map containing the
    * specified entries and additionally default entries specified in
    * {@link #DEFAULT_ENTRIES}.
    */
   private static Map<String, String> createUnmodifiableMapContainingDefaults(
         List<Entry> entries) {

      Map<String, String> mutableMap = new LinkedHashMap<>();

      /*
       * Add default entries.
       */
      for (Entry entry : DEFAULT_ENTRIES) {
         mutableMap.put(entry.key, entry.value);
      }

      /*
       * Add specified entries.
       */
      for (Entry entry : entries) {
         mutableMap.put(entry.key, entry.value);
      }

      /*
       * Convert to an unmodifiable map and return.
       */
      Map<String, String> unmodifiableMap = Collections
            .unmodifiableMap(mutableMap);
      return unmodifiableMap;
   }

   /**
    * File in which the present {@link ProofCollectionSettings} were declared.
    */
   private final File sourceProofCollectionFile;

   /**
    * String {@link Map} containing all settings entries.
    */
   private final Map<String, String> immutableSettingsMap;

   /**
    * Creates a base {@link ProofCollectionSettings} object from the specified
    * parameters with no parent settings. This method is called by
    * {@link ProofCollectionParser}.
    */
   ProofCollectionSettings(String proofCollectionFileLocation,
         List<Entry> entries) {
      /*
       * Determine source proof collection file from string location.
       */
      assert proofCollectionFileLocation != null : "Unexpected nullpointer detected - "
            + "no proof collection source file specified.";
      sourceProofCollectionFile = new File(proofCollectionFileLocation)
            .getParentFile();
      assert sourceProofCollectionFile.isAbsolute() : "Expecting location of source proof collection "
            + "file to be given as absolute path.";
      assert sourceProofCollectionFile.exists() : "Given source proof collection file does not exist.";

      /*
       * Warn about duplicate entries. We only do this in the constructor that
       * is called directly by ProofCollectionParser so that user is informed
       * about duplicate entries in proof collection text file.
       */
      Set<String> keys = new LinkedHashSet<>();
      for (Entry entry : entries) {
         String key = entry.key;
         if (keys.contains(key)) {
            System.out.println("Warning: The key \"" + key
                  + "\" is assigned multiple times in file: "
                  + sourceProofCollectionFile);
         }
         else {
            keys.add(key);
         }
      }

      /*
       * Compute immutable map containing settings entries.
       */
      immutableSettingsMap = createUnmodifiableMapContainingDefaults(entries);
   }

   /**
    * Creates a {@link ProofCollectionSettings} object that overrides an
    * existing {@link ProofCollectionSettings} object.
    */
   public ProofCollectionSettings(ProofCollectionSettings parentSettings,
         List<Entry> entries) {
      /*
       * Use source proof collection from parent settings.
       */
      this.sourceProofCollectionFile = parentSettings.sourceProofCollectionFile;

      /*
       * Create new list of entries containing parent entries and local entries.
       * Entries from parent ProofCollectionSettings are by local entries.
       */
      Set<String> localKeys = new LinkedHashSet<>();
      for (Entry entry : entries) {
         String key = entry.key;
         localKeys.add(key);
      }
      List<Entry> mergedEntries = new LinkedList<>(entries);
      for (Map.Entry<String, String> entry : parentSettings.immutableSettingsMap
            .entrySet()) {
         if (!localKeys.contains(entry.getKey())) {
            mergedEntries.add(new Entry(entry.getKey(), entry.getValue()));
         }
      }
      mergedEntries.addAll(entries);

      /*
       * Compute immutable map containing settings entries.
       */
      immutableSettingsMap = createUnmodifiableMapContainingDefaults(mergedEntries);
   }

   /**
    * Reads out generic settings, which were be specified as (key, value) pairs
    * during object creation.
    * 
    * @see Entry
    */
   public String get(String key) {
      return immutableSettingsMap.get(key);
   }

   public ForkMode getForkMode() {
      String forkMode = get(FORK_MODE);
      for (ForkMode mode : ForkMode.values()) {
         if (forkMode.toLowerCase().equals(mode.toString().toLowerCase())) {
            return mode;
         }
      }
      return ForkMode.NOFORK;
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
    * Static class for {@link ProofCollectionSettings} entries.
    */
   public static class Entry {
      public final String key, value;

      public Entry(String key, String value) {
         this.key = key;
         this.value = value;
      }
   }

}
