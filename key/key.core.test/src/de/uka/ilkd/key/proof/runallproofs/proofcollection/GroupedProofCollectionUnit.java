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
   private final ProofCollectionSettings settings;

   public GroupedProofCollectionUnit(String groupName,
         ProofCollectionSettings settings, List<TestFile> files) {
      this.groupName = groupName;
      this.settings = settings;
      this.testFiles = files;
   }

   @Override
   public RunAllProofsTestUnit createRunAllProofsTestUnit(String testName)
         throws IOException {
      return new RunAllProofsTestUnit(testName, settings, testFiles, false);
   }

   @Override
   String getName() {
      return groupName;
   }
}
