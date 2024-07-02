package de.uka.ilkd.key.proof.runallproofs;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import org.antlr.runtime.RecognitionException;

/**
 * Used by {@link RunAllProofsTest} command line interface to print out a list
 * of test cases. Command line interface can be found at git location:<br>
 * key/scripts/runAllProofs
 *
 * @author Kai Wallisch
 *
 * @see RunAllProofsTestSuite
 * @see RunAllProofsTest
 */
public class ListRunAllProofsTestCases {

    public static void main(String[] args) throws IOException, RecognitionException {
        List<RunAllProofsTestUnit> units = new LinkedList<RunAllProofsTestUnit>();
        units.addAll(RunAllProofsTest.parseIndexFile(RunAllProofsFunctional.INDEX_FILE).createRunAllProofsTestUnits());
        units.addAll(RunAllProofsTest.parseIndexFile(RunAllProofsInfFlow.INDEX_FILE).createRunAllProofsTestUnits());
        for (RunAllProofsTestUnit unit : units) {
            System.out.println(unit.getTestName());
        }
    }

}