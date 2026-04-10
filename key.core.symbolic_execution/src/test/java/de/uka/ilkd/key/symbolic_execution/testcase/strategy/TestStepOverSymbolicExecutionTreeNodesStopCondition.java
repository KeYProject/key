/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.testcase.strategy;

import java.io.IOException;
import java.util.Map;
import javax.xml.parsers.ParserConfigurationException;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.StepOverSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionGoalChooser;
import de.uka.ilkd.key.symbolic_execution.testcase.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;

import org.junit.jupiter.api.Test;
import org.xml.sax.SAXException;

/**
 * Tests for {@link StepOverSymbolicExecutionTreeNodesStopCondition} and
 * {@link SymbolicExecutionGoalChooser}. To do a step over the {@link CompoundStopCondition} is also
 * tested.
 *
 * @author Martin Hentschel
 */
public class TestStepOverSymbolicExecutionTreeNodesStopCondition
        extends AbstractSymbolicExecutionTestCase {
    /**
     * Does some step over tests on two branches with different number of symbolic execution tree
     * nodes to make sure that the stop conditions works correctly in combination with the goal
     * chooser.
     */
    @Test // weigl not prev. activated
    public void testStepOverOnTwoBranches() throws ProofInputException, IOException,
            ParserConfigurationException, SAXException, ProblemLoaderException {
        Map<String, String> originalTacletOptions = null;
        SymbolicExecutionEnvironment<DefaultUserInterfaceControl> env = null;
        boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
        // Define test settings
        String javaPathInkeyRepDirectory =
            "/set/stepOverOnTwoBranches/test/StepOverOnTwoBranches.java";
        String containerTypeName = "StepOverOnTwoBranches";
        final String methodFullName = "main";
        String oraclePathInkeyRepDirectoryFile =
            "/set/stepOverOnTwoBranches/oracle/StepOverOnTwoBranches";
        String oracleFileExtension = ".xml";
        // Create proof environment for symbolic execution
        try {
            originalTacletOptions = setDefaultTacletOptions(testCaseDirectory,
                javaPathInkeyRepDirectory, containerTypeName, methodFullName);
            setOneStepSimplificationEnabled(null, true);
            env = createSymbolicExecutionEnvironment(testCaseDirectory, javaPathInkeyRepDirectory,
                containerTypeName, methodFullName, null, false, false, false, false, false, false,
                false, false, false, true);
            // Create proof environment for symbolic execution
            // Make sure that initial tree is valid
            int oracleIndex = 0;
            assertSetTreeAfterStep(env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex,
                oracleFileExtension, testCaseDirectory);
            // Do steps
            stepInto(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex,
                oracleFileExtension, testCaseDirectory); // main method
            stepInto(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex,
                oracleFileExtension, testCaseDirectory); // if
            stepOver(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex,
                oracleFileExtension, testCaseDirectory); // i = 2
            stepOver(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex,
                oracleFileExtension, testCaseDirectory); // j = 3
            stepOver(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex,
                oracleFileExtension, testCaseDirectory); // x = valueLonger(i)
            stepOver(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex,
                oracleFileExtension, testCaseDirectory); // y = value(j)
            stepOver(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex,
                oracleFileExtension, testCaseDirectory); // z
            stepOver(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex,
                oracleFileExtension, testCaseDirectory); // zz
            stepOver(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex,
                oracleFileExtension, testCaseDirectory); // return statement
            stepOver(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex,
                oracleFileExtension, testCaseDirectory); // method return -2
            stepOver(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex,
                oracleFileExtension, testCaseDirectory); // end
        } finally {
            setOneStepSimplificationEnabled(null, originalOneStepSimplification);
            restoreTacletOptions(originalTacletOptions);
            if (env != null) {
                env.dispose();
            }
        }
    }
}
