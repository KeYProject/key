package de.uka.ilkd.key.proof.proverules;

import java.io.IOException;
import java.util.Collection;

import org.antlr.runtime.RecognitionException;

import de.uka.ilkd.key.proof.io.ProblemLoaderException;

/**
 * Used by {@link ProveRulesTest} command line interface to print out a list
 * of test cases. Command line interface can be found at git location:<br>
 * key/scripts/proveRules
 *
 * @author Kai Wallisch
 *
 */
public class ListProveRulesTestCases {

   public static void main(String[] args) throws IOException,
         RecognitionException, ProblemLoaderException {
      Collection<Object[]> units = ProveRulesTest.data();
      for (Object[] testParams : units) {
         System.out.println(testParams[0]);
      }
   }

}
