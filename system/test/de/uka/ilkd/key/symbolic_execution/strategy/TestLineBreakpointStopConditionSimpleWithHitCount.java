// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.strategy;

import java.io.IOException;
import java.util.HashMap;

import javax.xml.parsers.ParserConfigurationException;

import org.xml.sax.SAXException;

import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.LineBreakpoint;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;

/**
 * Tests for {@link LineBreakpoint}. Tests if execution stops at {@link JavaLineBreakpoint} correctly.
 * 
 * @author Marco Drebing
 */
public class TestLineBreakpointStopConditionSimpleWithHitCount extends AbstractSymbolicExecutionTestCase {
   public void testBreakpointStopCondition() throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      HashMap<String, String> originalTacletOptions = null;
      boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
      SymbolicExecutionEnvironment<CustomUserInterface> env=null;
      try{
         // Define test settings
         String javaPathInkeyRepDirectory = "examples/_testcase/set/lineBreakpointsWithHitcountTest/test/BreakpointStopCallerAndLoop.java";
         String containerTypeName = "BreakpointStopCallerAndLoop";
         final String methodFullName = "main";
         String oraclePathInkeyRepDirectoryFile = "examples/_testcase/set/lineBreakpointsWithHitcountTest/oracle/BreakpointStop";
         String oracleFileExtension = ".xml";
         // Store original settings of KeY
         originalTacletOptions = setDefaultTacletOptions(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName);
         setOneStepSimplificationEnabled(null, true);
         // Create proof environment for symbolic execution
         env = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, null, false, false, false, false, false, false, false);
         // Make sure that initial tree is valid
         int oracleIndex = 0;
         assertSetTreeAfterStep(env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
         IProgramMethod callerMain = searchProgramMethod(env.getServices(), "BreakpointStopCallerAndLoop", "main");
         IProgramMethod calleeMain = searchProgramMethod(env.getServices(), "BreakpointStopCallee", "main");
         IProgramMethod callerLoop = searchProgramMethod(env.getServices(), "BreakpointStopCallerAndLoop", "loop");
         CompoundStopCondition allBreakpoints = new CompoundStopCondition();
         LineBreakpoint firstBreakpoint = new LineBreakpoint(callerMain.getPositionInfo().getFileName(), 16, -1, callerMain, env.getBuilder().getProof(),null, true, false, 15, 21);
         LineBreakpoint secondBreakpoint = new LineBreakpoint(callerLoop.getPositionInfo().getFileName(), 10, 2, callerLoop, env.getBuilder().getProof(),null, true, false, 8, 13);
         LineBreakpoint thirdBreakpoint = new LineBreakpoint(calleeMain.getPositionInfo().getFileName(), 7, -1, calleeMain, env.getBuilder().getProof(),null, true, false, 6, 9);
         SymbolicExecutionBreakpointStopCondition bc = new SymbolicExecutionBreakpointStopCondition(firstBreakpoint, secondBreakpoint, thirdBreakpoint);
         allBreakpoints.addChildren(bc);
         env.getProof().getServices().setFactory(createNewProgramVariableCollectorFactory(bc));
         // Do steps
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);   
      }
      finally{
         setOneStepSimplificationEnabled(null, originalOneStepSimplification);
         restoreTacletOptions(originalTacletOptions);
         if(env!=null){
            env.dispose();
         }
      }
   }
}