package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit;
import de.uka.ilkd.key.proof.runallproofs.TestResult;

/**
 * A {@link ProofCollectionUnit} that is created from several {@link TestFile}s
 * grouped together.
 * 
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class GroupedProofCollectionUnit implements ProofCollectionUnit {

   private final String groupName;
   private final List<TestFile> testFiles;
   private final List<ProofCollectionSettings.Entry> settingsEntries;

   /**
    * A temp directory prefix is created for each group so that directories for
    * groups can easily be recognized in the {@link RunAllProofsTest} temp
    * directory.
    * 
    * @see de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit#getTempDirectoryPrefix()
    * @see de.uka.ilkd.key.proof.runallproofs.proofcollection.ForkedTestFileRunner
    */
   private final String tempDirectoryPrefix;

   public GroupedProofCollectionUnit(String groupName,
         List<ProofCollectionSettings.Entry> settingsEntries,
         List<TestFile> files) {
      this.groupName = groupName;
      this.settingsEntries = settingsEntries;
      this.testFiles = files;
      this.tempDirectoryPrefix = groupName + "-";
   }

   @Override
   public RunAllProofsTestUnit createRunAllProofsTestUnit(
         final ProofCollectionSettings parentSettings) {

      final ProofCollectionSettings settings = new ProofCollectionSettings(
            parentSettings, settingsEntries);

      return new RunAllProofsTestUnit(groupName) {

         @Override
         public TestResult runTest() throws Exception {

            /*
             * List of test results containing one test result for each test
             * file contained in this group.
             */
            List<TestResult> testResults;

            ForkMode forkMode = settings.getForkMode();
            if (forkMode == ForkMode.PERGROUP) {
               testResults = ForkedTestFileRunner.processTestFiles(testFiles,
                     settings, tempDirectoryPrefix);
            }
            else if (forkMode == ForkMode.NOFORK
                  || forkMode == ForkMode.PERFILE) {
               testResults = new ArrayList<>();
               for (TestFile testFile : testFiles) {
                  TestResult testResult = forkMode == ForkMode.NOFORK ? testFile
                        .runKey(settings) : ForkedTestFileRunner
                        .processTestFile(testFile, settings,
                              tempDirectoryPrefix);
                  testResults.add(testResult);
               }
            }
            else {
               throw new RuntimeException("Unexpected value for fork mode: "
                     + forkMode);
            }

            /*
             * Merge list of test results into one single test result.
             */
            boolean success = true;
            String message = "group " + groupName + ":\n";
            for (TestResult testResult : testResults) {
               success &= testResult.success;
               message += testResult.message + "\n";
            }
            return new TestResult(message, success);
         }

      };
   }
}
