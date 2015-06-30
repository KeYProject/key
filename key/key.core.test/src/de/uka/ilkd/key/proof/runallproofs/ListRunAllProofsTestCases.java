package de.uka.ilkd.key.proof.runallproofs;

import java.io.IOException;
import java.util.List;

import org.antlr.runtime.RecognitionException;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollection;

/**
 * Used by {@link RunAllProofsTest} command line interface to print out a list
 * of test cases. Command line interface can be found at git location:<br>
 * key/scripts/runAllProofs
 *
 * @author Kai Wallisch
 *
 */
public class ListRunAllProofsTestCases {

   public static void main(String[] args) throws IOException,
         RecognitionException {
      ProofCollection proofCollection = RunAllProofsTest.parseIndexFile();
      List<RunAllProofsTestUnit> units = proofCollection
            .createRunAllProofsTestUnits();
      for (RunAllProofsTestUnit unit : units) {
         System.out.println(unit.getTestName());
      }
   }

}
