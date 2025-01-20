/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.testcase.strategy;

import java.io.IOException;
import java.util.Map;
import javax.xml.parsers.ParserConfigurationException;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.LineBreakpoint;
import de.uka.ilkd.key.symbolic_execution.testcase.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;

import org.junit.jupiter.api.Test;
import org.xml.sax.SAXException;


public class TestLineBreakpointStopConditionSimpleWithLoopInvariant
        extends AbstractSymbolicExecutionTestCase {
    @Test
    public void testBreakpointStopCondition() throws ProofInputException, IOException,
            ParserConfigurationException, SAXException, ProblemLoaderException {
        SymbolicExecutionEnvironment<DefaultUserInterfaceControl> envMain = null;
        SymbolicExecutionEnvironment<DefaultUserInterfaceControl> envSomethingMain = null;
        SymbolicExecutionEnvironment<DefaultUserInterfaceControl> envSomethingLocalMain = null;
        Map<String, String> originalTacletOptions = null;
        boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
        try {
            // Define test settings
            String javaPathInkeyRepDirectory =
                "/set/lineBreakpointsWithLoopInvariantTest/test/ArrayUtil.java";
            String containerTypeName = "ArrayUtil";
            final String methodFullName = "indexOf";
            String oraclePathInkeyRepDirectoryFile =
                "/set/lineBreakpointsWithLoopInvariantTest/oracle/ArrayUtil";
            String oracleFileExtension = ".xml";
            // Store original settings of KeY
            originalTacletOptions = setDefaultTacletOptions(testCaseDirectory,
                javaPathInkeyRepDirectory, containerTypeName, methodFullName);
            setOneStepSimplificationEnabled(null, true);
            // Create proof environment for symbolic execution
            envMain = createSymbolicExecutionEnvironment(testCaseDirectory,
                javaPathInkeyRepDirectory, containerTypeName, methodFullName, null, false, true,
                true, true, false, false, false, false, false, false);
            // Make sure that initial tree is valid
            int oracleIndex = 0;
            assertSetTreeAfterStep(envMain.getBuilder(), oraclePathInkeyRepDirectoryFile,
                ++oracleIndex, oracleFileExtension, testCaseDirectory);
            IProgramMethod indexOfMethod =
                searchProgramMethod(envMain.getServices(), containerTypeName, "indexOf");
            // Test method main()
            CompoundStopCondition allBreakpoints = new CompoundStopCondition();
            LineBreakpoint mainBreakpoint =
                new LineBreakpoint(indexOfMethod.getPositionInfo().getFileName(), 21, -1,
                    indexOfMethod, envMain.getBuilder().getProof(), null, true, true, 13, 26);

            SymbolicExecutionBreakpointStopCondition bc =
                new SymbolicExecutionBreakpointStopCondition(mainBreakpoint);
            allBreakpoints.addChildren(bc);
            envMain.getProof().getServices()
                    .setFactory(createNewProgramVariableCollectorFactory(bc));

            // Suspend at breakpoint
            stepReturnWithBreakpoints(envMain.getUi(), envMain.getBuilder(),
                oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension,
                testCaseDirectory, allBreakpoints);

            // Finish symbolic execution
            stepReturnWithBreakpoints(envMain.getUi(), envMain.getBuilder(),
                oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension,
                testCaseDirectory, allBreakpoints);
        } finally {
            setOneStepSimplificationEnabled(null, originalOneStepSimplification);
            restoreTacletOptions(originalTacletOptions);
            if (envMain != null) {
                envMain.dispose();
            }
            if (envSomethingMain != null) {
                envSomethingMain.dispose();
            }
            if (envSomethingLocalMain != null) {
                envSomethingLocalMain.dispose();
            }
        }
    }
}
