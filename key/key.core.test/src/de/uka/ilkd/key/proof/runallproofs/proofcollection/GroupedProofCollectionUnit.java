package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.util.List;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestSubProcess;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit;
import de.uka.ilkd.key.proof.runallproofs.SuccessReport;

/**
 * A {@link ProofCollectionUnit} that is created from several {@link TestFile}s
 * grouped together.
 * 
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class GroupedProofCollectionUnit implements ProofCollectionUnit {

   private final String groupName;
   private final List<TestFile> files;
   private final List<ProofCollectionSettings.Entry> settingsEntries;

   public GroupedProofCollectionUnit(String groupName,
         List<ProofCollectionSettings.Entry> settingsEntries,
         List<TestFile> files) {
      this.groupName = groupName;
      this.settingsEntries = settingsEntries;
      this.files = files;
   }

   @Override
   public RunAllProofsTestUnit createRunAllProofsTestUnit(
         final ProofCollectionSettings parentSettings) {

      final ProofCollectionSettings settings = ProofCollectionSettingsFactory
            .createSettings(parentSettings, settingsEntries);

      return new RunAllProofsTestUnit() {
         /**
          * A temp directory prefix is created for each group so that directories for
          * groups can easily be recognized in the {@link RunAllProofsTest} temp directory.
          * 
          * @see de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit#getTempDirectoryPrefix()
          * @see de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestSubProcess
          */
         @Override
         public String getTempDirectoryPrefix() {
            return groupName + "-";
         }

         @Override
         public SuccessReport runTest() throws Exception {
            boolean success = true;
            String message = "group " + groupName + "\n";
            for (TestFile file : files) {
               SuccessReport report = file.runKey(settings);
               success &= report.success;
               message += report.message + "\n";
            }
            return new SuccessReport(message, success);
         }

      };
   }
}
