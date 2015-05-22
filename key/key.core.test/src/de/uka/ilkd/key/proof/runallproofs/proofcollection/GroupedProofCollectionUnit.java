package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit;
import de.uka.ilkd.key.proof.runallproofs.TestResult;

/**
 * A {@link ProofCollectionUnit} that is created from several {@link TestFile}s
 * that are grouped together.
 * 
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class GroupedProofCollectionUnit extends ProofCollectionUnit {

   private final String groupName;
   private final List<TestFile> testFiles;
   private final List<ProofCollectionSettings.Entry> settingsEntries;

   public GroupedProofCollectionUnit(String groupName,
         List<ProofCollectionSettings.Entry> settingsEntries,
         List<TestFile> files) {
      this.groupName = groupName;
      this.settingsEntries = settingsEntries;
      this.testFiles = files;
   }

   @Override
   public RunAllProofsTestUnit createRunAllProofsTestUnit(
         final ProofCollectionSettings parentSettings) throws IOException {

      final ProofCollectionSettings settings = new ProofCollectionSettings(
            parentSettings, settingsEntries);

      return new RunAllProofsTestUnit(groupName, settings, getTempDirectory(groupName), testFiles, false);

   }
}
