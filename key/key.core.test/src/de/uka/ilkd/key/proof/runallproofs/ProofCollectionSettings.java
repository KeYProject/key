package de.uka.ilkd.key.proof.runallproofs;

import java.io.File;
import java.io.Serializable;
import java.util.HashMap;
import java.util.Map;

public class ProofCollectionSettings implements Serializable {

   private static final String BASE_DIRECTORY_KEY = "baseDirectory";

   public final File proofCollectionFile;
   private final Map<String, Object> settingsMap = new HashMap<>();

   public ProofCollectionSettings(String proofCollectionFileLocaton) {
      proofCollectionFile = new File(proofCollectionFileLocaton)
            .getParentFile();
   }

   public Object put(String key, Object value) {
      if (settingsMap.containsKey(key)) {
         throw new RuntimeException("Overwriting keys not allowed in "
               + ProofCollectionSettings.class.getSimpleName());
      }
      return settingsMap.put(key, value);
   }

}
