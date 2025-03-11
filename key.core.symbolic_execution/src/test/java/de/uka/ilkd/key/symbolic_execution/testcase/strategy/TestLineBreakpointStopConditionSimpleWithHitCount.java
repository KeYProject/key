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

/**
 * Tests for {@link LineBreakpoint}. Tests if execution stops at {@link JavaLineBreakpoint}
 * correctly.
 *
 * @author Marco Drebing
 */
public class TestLineBreakpointStopConditionSimpleWithHitCount
        extends AbstractSymbolicExecutionTestCase {
    @Test // weigl not prev. activated
    public void testBreakpointStopCondition() throws ProofInputException, IOException,
            ParserConfigurationException, SAXException, ProblemLoaderException {
        Map<String, String> originalTacletOptions = null;
        boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
        SymbolicExecutionEnvironment<DefaultUserInterfaceControl> env = null;
        try {
            // Define test settings
            String javaPathInkeyRepDirectory =
                "/set/lineBreakpointsWithHitcountTest/test/BreakpointStopCallerAndLoop.java";
            String containerTypeName = "BreakpointStopCallerAndLoop";
            final String methodFullName = "main";
            String oraclePathInkeyRepDirectoryFile =
                "/set/lineBreakpointsWithHitcountTest/oracle/BreakpointStop";
            String oracleFileExtension = ".xml";
            // Store original settings of KeY
            originalTacletOptions = setDefaultTacletOptions(testCaseDirectory,
                javaPathInkeyRepDirectory, containerTypeName, methodFullName);
            setOneStepSimplificationEnabled(null, true);
            // Create proof environment for symbolic execution
            env = createSymbolicExecutionEnvironment(testCaseDirectory, javaPathInkeyRepDirectory,
                containerTypeName, methodFullName, null, false, false, false, false, false, false,
                false, false, false, true);
            // Make sure that initial tree is valid
            int oracleIndex = 0;
            assertSetTreeAfterStep(env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex,
                oracleFileExtension, testCaseDirectory);
            IProgramMethod callerMain =
                searchProgramMethod(env.getServices(), "BreakpointStopCallerAndLoop", "main");
            IProgramMethod calleeMain =
                searchProgramMethod(env.getServices(), "BreakpointStopCallee", "main");
            IProgramMethod callerLoop =
                searchProgramMethod(env.getServices(), "BreakpointStopCallerAndLoop", "loop");
            CompoundStopCondition allBreakpoints = new CompoundStopCondition();
            LineBreakpoint firstBreakpoint =
                new LineBreakpoint(callerMain.getPositionInfo().getFileName(), 16, -1, callerMain,
                    env.getBuilder().getProof(), null, true, false, 15, 21);
            LineBreakpoint secondBreakpoint =
                new LineBreakpoint(callerLoop.getPositionInfo().getFileName(), 10, 2, callerLoop,
                    env.getBuilder().getProof(), null, true, false, 8, 13);
            LineBreakpoint thirdBreakpoint =
                new LineBreakpoint(calleeMain.getPositionInfo().getFileName(), 7, -1, calleeMain,
                    env.getBuilder().getProof(), null, true, false, 6, 9);
            SymbolicExecutionBreakpointStopCondition bc =
                new SymbolicExecutionBreakpointStopCondition(firstBreakpoint, secondBreakpoint,
                    thirdBreakpoint);
            allBreakpoints.addChildren(bc);
            env.getProof().getServices().setFactory(createNewProgramVariableCollectorFactory(bc));
            // Do steps
            stepReturnWithBreakpoints(env.getUi(), env.getBuilder(),
                oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension,
                testCaseDirectory, allBreakpoints);
            stepReturnWithBreakpoints(env.getUi(), env.getBuilder(),
                oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension,
                testCaseDirectory, allBreakpoints);
            stepReturnWithBreakpoints(env.getUi(), env.getBuilder(),
                oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension,
                testCaseDirectory, allBreakpoints);
            stepReturnWithBreakpoints(env.getUi(), env.getBuilder(),
                oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension,
                testCaseDirectory, allBreakpoints);
            stepReturnWithBreakpoints(env.getUi(), env.getBuilder(),
                oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension,
                testCaseDirectory, allBreakpoints);
            stepReturnWithBreakpoints(env.getUi(), env.getBuilder(),
                oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension,
                testCaseDirectory, allBreakpoints);
            stepReturnWithBreakpoints(env.getUi(), env.getBuilder(),
                oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension,
                testCaseDirectory, allBreakpoints);
        } finally {
            setOneStepSimplificationEnabled(null, originalOneStepSimplification);
            restoreTacletOptions(originalTacletOptions);
            if (env != null) {
                env.dispose();
            }
        }
    }
}
