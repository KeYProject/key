package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.IOException;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit;

/**
 * Data structure for parse results of {@link ProofCollectionParser}. Method
 * {@link #createRunAllProofsTestUnits()} can be used to create a {@link List}
 * of {@link RunAllProofsTestUnit}s from an object of this class.
 * 
 * @author Kai Wallisch
 *
 */
public final class ProofCollection {

   private final List<ProofCollectionUnit> units = new LinkedList<>();
   private final ProofCollectionSettings settings;

   ProofCollection(ProofCollectionSettings settings) {
      this.settings = settings;
   }

   void add(ProofCollectionUnit unit) {
      units.add(unit);
   }

   /**
    * Create list of {@link RunAllProofsTestUnit}s from list of
    * {@link ProofCollectionUnit}s.
    * 
    * @return A list of {@link RunAllProofsTestUnit}s.
    * @throws IOException
    *            Names of {@link SingletonProofCollectionUnit}s are determined
    *            by their corresponding file names. In case file name can't be
    *            read {@link IOException} may be thrown.
    */
   public List<RunAllProofsTestUnit> createRunAllProofsTestUnits()
         throws IOException {

      List<RunAllProofsTestUnit> ret = new LinkedList<>();

      Set<String> testCaseNames = new LinkedHashSet<>();
      for (ProofCollectionUnit proofCollectionUnit : units) {

         final String proposedTestCaseName = proofCollectionUnit.getName();
         String testCaseName = proposedTestCaseName;
         int counter = 0;
         while (testCaseNames.contains(testCaseName)) {
            counter++;
            testCaseName = proposedTestCaseName + "#" + counter;
         }
         testCaseNames.add(testCaseName);

         RunAllProofsTestUnit testUnit = proofCollectionUnit
               .createRunAllProofsTestUnit(testCaseName);
         ret.add(testUnit);
      }

      Set<String> enabledTestCaseNames = settings.getEnabledTestCaseNames();
      if (enabledTestCaseNames == null) {
         return ret;
      }
      else {
         Iterator<RunAllProofsTestUnit> iterator = ret.iterator();
         while (iterator.hasNext()) {
            RunAllProofsTestUnit unit = iterator.next();
            if (!enabledTestCaseNames.contains(unit.getTestName())) {
               iterator.remove();
            }
         }
         return ret;
      }
   }

   public ProofCollectionSettings getSettings() {
      return settings;
   }

}
