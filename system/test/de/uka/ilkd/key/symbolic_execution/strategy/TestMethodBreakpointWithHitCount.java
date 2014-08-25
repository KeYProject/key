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
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.MethodBreakpoint;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;

public class TestMethodBreakpointWithHitCount extends AbstractSymbolicExecutionTestCase {
   public void testBreakpointStopCondition() throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      SymbolicExecutionEnvironment<CustomUserInterface> env=null;
      HashMap<String, String> originalTacletOptions = null;
      boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
      try{
         // Define test settings
         String javaPathInkeyRepDirectory = "examples/_testcase/set/methodBreakpointsWithHitcountTest/test/BreakpointStopCallerAndLoop.java";
         String containerTypeName = "BreakpointStopCallerAndLoop";
         final String methodFullName = "main";
         String oraclePathInkeyRepDirectoryFile = "examples/_testcase/set/methodBreakpointsWithHitcountTest/oracle/MethodBreakpointStop";
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
         //on method call and return
         MethodBreakpoint inAndOutBreakpoint = new MethodBreakpoint(callerMain.getPositionInfo().getFileName(), 15, -1, callerMain, env.getBuilder().getProof(),null, true, false, 15, 24,true,true);
         //on method call with hitcount
         MethodBreakpoint hitCountBreakpoint = new MethodBreakpoint(callerLoop.getPositionInfo().getFileName(), 8, 2, callerLoop, env.getBuilder().getProof(),null, true, false, 8, 13, true, false);
         //on method return with hitcount
         MethodBreakpoint thirdBreakpoint = new MethodBreakpoint(calleeMain.getPositionInfo().getFileName(), 6, 2, calleeMain, env.getBuilder().getProof(),null, true, false, 6, 9, false, true);
         SymbolicExecutionBreakpointStopCondition bc = new SymbolicExecutionBreakpointStopCondition(inAndOutBreakpoint,hitCountBreakpoint,thirdBreakpoint);
         allBreakpoints.addChildren(bc);
         env.getProof().getServices().setFactory(createNewProgramVariableCollectorFactory(bc));
         // Do steps
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