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

      return new RunAllProofsTestUnit(testName, settings) {

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
                     getTempDir());
            }
            else if (forkMode == ForkMode.NOFORK
                  || forkMode == ForkMode.PERFILE) {
               testResults = new ArrayList<>();
               for (TestFile testFile : testFiles) {
                  TestResult testResult = forkMode == ForkMode.NOFORK ? testFile
                        .runKey() : ForkedTestFileRunner.processTestFile(
                        testFile, getTempDir());
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

   @Override
   String getName() {
      return groupName;
   }
}
