package de.uka.ilkd.key.proof.runallproofs;

import java.util.List;
import java.util.Map;

/**
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class GroupedProofCollectionUnit extends ProofCollectionUnit {

   final String groupName;
   List<TestFile> files;
   private final Map<String, String> settingsMap;

   public GroupedProofCollectionUnit(String groupName,
         Map<String, String> settingsMap, List<TestFile> files) {
      this.groupName = groupName;
      this.settingsMap = settingsMap;

      if (this.settingsMap.size() > 0) {
         // TODO decide whether local settings map is really necessary
         throw new UnsupportedOperationException(
               "Local settings map not supported at the moment.");
      }

      this.files = files;
   }

   @Override
   public SuccessReport processProofObligations(
         ProofCollectionSettings parentSettings) throws Exception {
      ProofCollectionSettings settings = parentSettings;

      boolean success = true;
      String message = "group " + groupName + "\n";
      for (TestFile file : files) {
         SuccessReport report = file.runKey(settings);
         success &= report.success;
         message += report.message + "\n";
      }
      return new SuccessReport(message, success);
   }

   @Override
   public String getTempDirectoryPrefix() {
      return groupName + "-";
   }

}
