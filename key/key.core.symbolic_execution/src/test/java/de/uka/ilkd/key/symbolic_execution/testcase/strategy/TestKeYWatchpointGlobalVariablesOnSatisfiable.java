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

package de.uka.ilkd.key.symbolic_execution.testcase.strategy;

import java.io.IOException;
import java.util.HashMap;

import javax.xml.parsers.ParserConfigurationException;

import org.xml.sax.SAXException;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.KeYWatchpoint;
import de.uka.ilkd.key.symbolic_execution.testcase.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;

public class TestKeYWatchpointGlobalVariablesOnSatisfiable extends AbstractSymbolicExecutionTestCase {
   public void testBreakpointStopCondition() throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      SymbolicExecutionEnvironment<DefaultUserInterfaceControl> env=null;
      HashMap<String, String> originalTacletOptions = null;
      boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
      try{
         // Define test settings
         String javaPathInkeyRepDirectory = "/set/keyWatchpointGlobalVariablesOnSatisfiable/test/GlobalVariablesOnSatisfiable.java";
         String containerTypeName = "GlobalVariablesOnSatisfiable";
         final String methodFullName = "doSomething";
         String oraclePathInkeyRepDirectoryFile = "/set/keyWatchpointGlobalVariablesOnSatisfiable/oracle/GlobalVariablesOnSatisfiable";
         String oracleFileExtension = ".xml";
         // Store original settings of KeY
         originalTacletOptions = setDefaultTacletOptions(testCaseDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName);
         setOneStepSimplificationEnabled(null, true);
         // Create proof environment for symbolic execution
         env = createSymbolicExecutionEnvironment(testCaseDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, null, false, false, false, false, false, false, false, false, false, true);
         // Make sure that initial tree is valid
         int oracleIndex = 0;
         assertSetTreeAfterStep(env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory);
         CompoundStopCondition allBreakpoints = new CompoundStopCondition();
         JavaInfo javaInfo = env.getServices().getJavaInfo();
         KeYJavaType containerType = javaInfo.getTypeByClassName(containerTypeName);
         
         KeYWatchpoint globalVariableCondition = new KeYWatchpoint(-1, env.getBuilder().getProof(),"x_global==17", true, true, containerType, false);
         
         SymbolicExecutionBreakpointStopCondition bc = new SymbolicExecutionBreakpointStopCondition(globalVariableCondition);
         allBreakpoints.addChildren(bc);
         env.getProof().getServices().setFactory(createNewProgramVariableCollectorFactory(bc));
         // Do steps
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory, allBreakpoints);
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory, allBreakpoints);
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory, allBreakpoints);
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory, allBreakpoints);
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory, allBreakpoints);
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory, allBreakpoints);
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