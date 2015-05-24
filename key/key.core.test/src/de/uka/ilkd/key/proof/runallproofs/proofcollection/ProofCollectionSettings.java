package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.File;
import java.io.IOException;
import java.io.Serializable;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest;
import static de.uka.ilkd.key.proof.runallproofs.proofcollection.TestFile.getAbsoluteFile;
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
   private static final String STATISTICS_FILE = "statisticsFile";
   private static final String RELOAD_ENABLED = "reloadEnabled";
   private static final String TEMP_DIR = "tempDir";

   /**
    * File in which the present {@link ProofCollectionSettings} were declared.
    */
   private final File sourceProofCollectionFile;

   /**
    * String {@link Map} containing all settings entries.
    */
   private final Map<String, String> immutableSettingsMap;

   /**
    * File in which statistics are written.
    */
   private final StatisticsFile statisticsFile;

   /**
    * {@link List} of settings entries that are created from system properties.
    * Those entries are copied into every {@link ProofCollectionSettings}
    * object. Every system property starting with "key.runallproofs." is
    * considered a RunAllProofs setting. It overrides settings specified in the
    * automaticJAVADL.txt index file. RunAllProofs settings can be specified via
    * system properties by providing JVM arguments like:
    * "-Dkey.runallproofs.forkMode=perFile"
    */
   private static final List<Entry<String, String>> SYSTEM_PROPERTIES_ENTRIES;
   static {
      /*
       * Iterating over all system properties to get settings entries. System
       * properties starting with "key.runallproofs." are relevant for proof
       * collection settings.
       */
      List<Entry<String, String>> tmp = new LinkedList<>();
      Set<Entry<Object, Object>> entrySet = System.getProperties().entrySet();
      for (Entry<Object, Object> entry : entrySet) {
         String key = (String) entry.getKey();
         String value = (String) entry.getValue();
         if (key.startsWith("key.runallproofs.")) {
            key = key.substring(17);// strip "key.runallproofs." from key
            tmp.add(getSettingsEntry(key, value));
         }
      }
      SYSTEM_PROPERTIES_ENTRIES = Collections.unmodifiableList(tmp);
   }

   /**
    * Converts a list of map entries to an unmodifiable map containing the
    * specified entries and additionally default entries specified in
    * {@link #SYSTEM_PROPERTIES_ENTRIES}.
    */
   private static Map<String, String> createUnmodifiableMapContainingDefaults(
         List<Entry<String, String>> entries) {

      Map<String, String> mutableMap = new LinkedHashMap<>();

      /*
       * Add specified entries.
       */
      for (Entry<String, String> entry : entries) {
         mutableMap.put(entry.getKey(), entry.getValue());
      }

      /*
       * Add entries created from system properties.
       */
      for (Entry<String, String> entry : SYSTEM_PROPERTIES_ENTRIES) {
         mutableMap.put(entry.getKey(), entry.getValue());
      }

      /*
       * Convert to an unmodifiable map and return.
       */
      Map<String, String> unmodifiableMap = Collections
            .unmodifiableMap(mutableMap);
      return unmodifiableMap;
   }

   /**
    * Creates a {@link ProofCollectionSettings} object from the specified
    * parameters with no parent settings.
    */
   ProofCollectionSettings(String proofCollectionFileLocation,
         List<Entry<String, String>> entries) {
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
       * Compute immutable map containing settings entries.
       */
      immutableSettingsMap = createUnmodifiableMapContainingDefaults(entries);

      /*
       * Compute location of statistics file.
       */
      String statisticsFileName = get(STATISTICS_FILE);
      if (statisticsFileName == null) {
         statisticsFile = null;
      }
      else {
         statisticsFile = new StatisticsFile(getAbsoluteFile(
               getBaseDirectory(), statisticsFileName));
      }
   }

   /**
    * Creates a {@link ProofCollectionSettings} object that overrides an
    * existing {@link ProofCollectionSettings} object.
    */
   public ProofCollectionSettings(ProofCollectionSettings parentSettings,
         List<Entry<String, String>> entries) {
      /*
       * Use source proof collection from parent settings.
       */
      this.sourceProofCollectionFile = parentSettings.sourceProofCollectionFile;

      /*
       * Create new list of entries containing parent entries and local entries.
       * Entries from parent ProofCollectionSettings are by local entries.
       */
      Set<String> localKeys = new LinkedHashSet<>();
      for (Entry<String, String> entry : entries) {
         String key = entry.getKey();
         localKeys.add(key);
      }
      List<Entry<String, String>> mergedEntries = new LinkedList<>(entries);
      for (Entry<String, String> entry : parentSettings.immutableSettingsMap
            .entrySet()) {
         if (!localKeys.contains(entry.getKey())) {
            mergedEntries.add(entry);
         }
      }
      mergedEntries.addAll(entries);

      /*
       * Compute immutable map containing settings entries.
       */
      immutableSettingsMap = createUnmodifiableMapContainingDefaults(mergedEntries);

      /*
       * Inherit statistics file from parent settings.
       */
      statisticsFile = parentSettings.getStatisticsFile();
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

      ForkMode forkMode = null;
      String forkModeString = get(FORK_MODE);

      if (forkModeString == null || forkModeString.length() == 0) {
         // Return default value in case no particular fork mode is
         // specified.
         forkMode = ForkMode.NOFORK;
      }
      else {
         for (ForkMode mode : ForkMode.values()) {
            if (mode.settingName.toLowerCase().equals(
                  forkModeString.toLowerCase())) {
               forkMode = mode;
               break;
            }
         }
      }

      /*
       * Warn user that specified fork mode was not recognized but use default
       * fork mode rather than throwing an Exception.
       */
      if (forkMode == null) {
         /*
          * Unknown value used for fork mode. Printing out warning to the user.
          */
         System.out
               .println("Warning: Unknown value used for runAllProofs fork mode: "
                     + forkModeString);
         System.out
               .println("Use either of the following: noFork (default), perGroup, perFile");
         System.out.println("Using default fork mode: noFork");
         System.out
               .println("If you want to inspect source code, look up the following location:");
         System.out.println(new Throwable().getStackTrace()[0]);
         forkMode = ForkMode.NOFORK;
      }

      return forkMode;
   }

   /**
    * Returns KeY settings that will be used as default settings.
    */
   public String getGlobalKeYSettings() {
      String gks = get(KEY_SETTINGS_KEY);
      return gks == null ? "" : gks;
   }

   /**
    * Settings must specify a base directory. Relative
    * {@link ProofCollectionSettings} paths will be treated as relative to
    * directory returned by this method.
    */
   public File getBaseDirectory() {
      String baseDirectoryName = get(BASE_DIRECTORY_KEY);
      return baseDirectoryName == null ? sourceProofCollectionFile
            .getParentFile() : getAbsoluteFile(sourceProofCollectionFile,
            baseDirectoryName);
   }

   /**
    * Returns location of statistics file. Can be null. In this case no
    * statistics are saved.
    */
   public StatisticsFile getStatisticsFile() {
      return statisticsFile;
   }

   public File getTempDir() throws IOException {
      String tempDirString = get(TEMP_DIR);
      if (tempDirString == null) {
         throw new IOException(
               "No temporary directory specified in RunAllProofs configuration file. "
                     + "Cannot run in forked mode. "
                     + "To solve this, specify setting \"" + TEMP_DIR
                     + "\" in file " + sourceProofCollectionFile);
      }
      File tempDir = new File(tempDirString);
      if (!tempDir.isAbsolute()) {
         tempDir = new File(getBaseDirectory(), tempDirString);
      }
      if (tempDir.isFile()) {
         throw new IOException("Specified temporary directory is a file: "
               + tempDir + "\n" + "Configure temporary directory in file "
               + sourceProofCollectionFile + " to solve this.");
      }
      return tempDir;
   }

   /**
    * Retrieve names of test cases that are configured to be enabled. By
    * default, all {@link RunAllProofsTest} test cases are enabled. If this
    * method returns something else than null, then only test cases whose name
    * is contained in the returned set are enabled.
    */
   public Set<String> getEnabledTestCaseNames() {
      String testCases = get("testCases");
      if (testCases == null || testCases.length() == 0) {
         return null;
      }

      Set<String> enabledTestCaseNames = new LinkedHashSet<>();
      String[] testCaseList = testCases.split(",");
      for (String testCaseName : testCaseList) {
         enabledTestCaseNames.add(testCaseName);
      }
      enabledTestCaseNames = Collections.unmodifiableSet(enabledTestCaseNames);
      return enabledTestCaseNames;
   }

   /**
    * Check whether proof reloading is enabled or disabled. If enabled, closed
    * proofs will be saved and reloaded after prover is finished.
    */
   public boolean reloadEnabled() {
      String reloadEnabled = get(RELOAD_ENABLED);
      if (reloadEnabled == null || reloadEnabled.equals("true")
            || reloadEnabled.equals("")) {
         return true;
      }
      else if (reloadEnabled.equals("false")) {
         return false;
      }
      else {
         System.out.println("Warning - unrecognized reload option: "
               + reloadEnabled);
         System.out.println("To check Java code for this message, see:");
         System.out.println(new Throwable().getStackTrace()[0]);
         return true;
      }
   }

   /**
    * Static method for creation of {@link ProofCollectionSettings} entries.
    */
   public static Entry<String, String> getSettingsEntry(final String key,
         final String value) {
      return new Entry<String, String>() {

         @Override
         public String getKey() {
            return key;
         }

         @Override
         public String getValue() {
            return value;
         }

         @Override
         public String setValue(String value) {
            throw new UnsupportedOperationException(
                  "Proof collection settings are immutable. Changing settings values is not allowed.");
         }
      };
   }

}
