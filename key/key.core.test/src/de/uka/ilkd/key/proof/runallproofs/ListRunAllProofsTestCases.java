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
 */
public class ListRunAllProofsTestCases {

    public static void main(String[] args) throws IOException, RecognitionException {
        List<RunAllProofsTestUnit> units = new LinkedList<RunAllProofsTestUnit>();
        for (String s: RunAllProofsTest.PROOF_INDEX) {
            units.addAll(RunAllProofsTest.parseIndexFile(s).createRunAllProofsTestUnits());
        }
        for (RunAllProofsTestUnit unit : units) {
            System.out.println(unit.getTestName());
        }
    }

}