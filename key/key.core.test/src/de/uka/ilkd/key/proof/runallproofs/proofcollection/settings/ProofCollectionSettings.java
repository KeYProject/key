package de.uka.ilkd.key.proof.runallproofs.proofcollection.settings;

import java.io.File;
import java.io.Serializable;

/**
 * Immutable settings object for proof collections. Use class
 * {@link ProofCollectionSettingsFactory} to get instances of this class. Note:
 * In case KeY will be migrated to Java8, the (static) factory methods can be
 * moved to this class.
 * 
 * @author Kai Wallisch
 *
 */
public interface ProofCollectionSettings extends Serializable {

   public static final String BASE_DIRECTORY_KEY = "baseDirectory";

   /**
    * Reads out generic settings, which were be specified as (key, value) pairs
    * during object creation.
    * 
    * @see Entry
    */
   public String get(String key);

   /**
    * Returns KeY settings that will be used as default settings.
    */
   public String getGlobalKeYSettings();

   /**
    * Returns the file in which the present {@link ProofCollectionSettings} were
    * declared.
    */
   public File getSourceProofCollectionFile();

   /**
    * Settings must specify a base directory. Relative paths can be treated as
    * relative to directory returned by this method.
    */
   public File getBaseDirectory();

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
