package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.IOException;
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
public class ProofCollection {

   private final List<ProofCollectionUnit> units;
   private final ProofCollectionSettings settings;

   ProofCollection(List<ProofCollectionUnit> units,
         ProofCollectionSettings settings) {
      this.units = units;
      this.settings = settings;
   }

   /**
    * Converts this {@link ProofCollection} into a list of
    * {@link RunAllProofsTestUnit}s.
    * 
    * @return A list of {@link RunAllProofsTestUnit}s.
    * @throws IOException
    *            Names of {@link SingletonProofCollectionUnit}s are determined
    *            by their corresponding file names. In case file name can't be
    *            read {@link IOException} may be thrown.
    */
   public List<RunAllProofsTestUnit> createRunAllProofsTestUnits()
         throws IOException {

      /**
       * Create list of {@link RunAllProofsTestUnit}s from list of units. This
       * procedure avoids duplicate names for different test units.
       */
      List<RunAllProofsTestUnit> ret = new LinkedList<>();
      Set<String> testUnitNames = new LinkedHashSet<>();
      for (ProofCollectionUnit proofCollectionUnit : units) {

         RunAllProofsTestUnit testUnit = proofCollectionUnit
               .createRunAllProofsTestUnit(settings);
         String testUnitOriginalName = testUnit.name;

         /**
          * Assign a new name to testUnit in case one of the previous
          * {@link RunAllProofsTestUnit}s occupies its name already.
          */
         String testUnitName = testUnitOriginalName;
         int counter = 0;
         while (testUnitNames.contains(testUnitName)) {
            counter++;
            testUnitName = testUnitOriginalName + "#" + counter;
         }
         testUnit.name = testUnitName;
         testUnitNames.add(testUnitName);

         ret.add(testUnit);
      }

      return ret;
   }
}
