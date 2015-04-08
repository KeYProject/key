package de.uka.ilkd.key.proof.runallproofs;

import java.io.File;
import java.io.Serializable;
import java.util.Map;
import static de.uka.ilkd.key.proof.runallproofs.FileWithTestProperty.getAbsoluteFile;

public class ProofCollectionSettings implements Serializable {

   public final File initialDirectory;
   private static final String INITIAL_DIRECTORY_KEY = "initialDirectory";

   public ProofCollectionSettings(Map<String, String> settingsMap,
         String sourceFileName) {

      File sourceFileDir = new File(sourceFileName).getParentFile();
      assert sourceFileDir.isAbsolute() : "Expecting antlr to provide absolute path to source "
            + "file, but found" + sourceFileName;

      initialDirectory = settingsMap.containsKey(INITIAL_DIRECTORY_KEY) ? getAbsoluteFile(
            sourceFileDir, settingsMap.get(INITIAL_DIRECTORY_KEY)) : sourceFileDir;
   }
}
