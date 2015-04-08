package de.uka.ilkd.key.proof.runallproofs;

import java.io.IOException;
import java.util.List;
import java.util.Map;

/**
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class GroupedProofCollectionUnit extends ProofCollectionUnit {

   final String groupName;
   List<FileWithTestProperty> files;
   private final Map<String, String> settingsMap;

   public GroupedProofCollectionUnit(String groupName,
         Map<String, String> settingsMap, List<FileWithTestProperty> files) {
      this.groupName = groupName;
      this.settingsMap = settingsMap;
      
      if(this.settingsMap.size() > 0){
         // TODO decide whether local settings map is really necessary
         throw new UnsupportedOperationException("Local settings map not supported at the moment.");
      }
      
      this.files = files;
   }

   @Override
   public boolean processProofObligations(ProofCollectionSettings parentSettings)
         throws IOException {
      ProofCollectionSettings settings = parentSettings;
      
      System.out.println("group " + groupName);
      for (FileWithTestProperty file : files) {
         System.out.println(file.testProperty + " " + file.getFile(settings));
      }
      System.out.println();
      return true;
   }

}
