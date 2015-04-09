package de.uka.ilkd.key.proof.runallproofs;

import java.io.File;
import java.io.Serializable;
import java.util.Map;
import static de.uka.ilkd.key.proof.runallproofs.FileWithTestProperty.getAbsoluteFile;

public class ProofCollectionSettings implements Serializable {

   public final File baseDirectory;
   private static final String BASE_DIRECTORY_KEY = "baseDirectory";

   public ProofCollectionSettings(Map<String, String> settingsMap,
         String sourceFileName) {

      File sourceFileDir = new File(sourceFileName).getParentFile();
      assert sourceFileDir.isAbsolute() : "Expecting antlr to provide absolute path to source "
            + "file, but found" + sourceFileName;

      baseDirectory = settingsMap.containsKey(BASE_DIRECTORY_KEY) ? getAbsoluteFile(
            sourceFileDir, settingsMap.get(BASE_DIRECTORY_KEY)) : sourceFileDir;
   }
}
