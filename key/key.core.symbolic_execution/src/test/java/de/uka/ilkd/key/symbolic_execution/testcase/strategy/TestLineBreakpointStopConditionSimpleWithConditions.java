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
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.LineBreakpoint;
import de.uka.ilkd.key.symbolic_execution.testcase.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;

public class TestLineBreakpointStopConditionSimpleWithConditions extends AbstractSymbolicExecutionTestCase {
   public void testBreakpointStopCondition() throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      SymbolicExecutionEnvironment<DefaultUserInterfaceControl> envMain=null;
      SymbolicExecutionEnvironment<DefaultUserInterfaceControl> envSomethingMain=null;
      SymbolicExecutionEnvironment<DefaultUserInterfaceControl> envSomethingLocalMain=null;
      HashMap<String, String> originalTacletOptions = null;
      boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
      try{
         // Define test settings
         String javaPathInkeyRepDirectory = "/set/lineBreakpointsWithConditionsTest/test/SimpleConditionExample.java";
         String containerTypeName = "SimpleConditionExample";
         final String methodFullName = "main";
         String oraclePathInkeyRepDirectoryFile = "/set/lineBreakpointsWithConditionsTest/oracle/BreakpointStopConditionWithCondition";
         String oracleFileExtension = ".xml";
         // Store original settings of KeY
         originalTacletOptions = setDefaultTacletOptions(testCaseDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName);
         setOneStepSimplificationEnabled(null, true);
         // Create proof environment for symbolic execution
         envMain = createSymbolicExecutionEnvironment(testCaseDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, null, false, false, false, false, false, false, false, false, false, false);
         // Make sure that initial tree is valid
         int oracleIndex = 0;
         assertSetTreeAfterStep(envMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory);
         IProgramMethod main = searchProgramMethod(envMain.getServices(), containerTypeName, "main");
         // Test  method main()
         CompoundStopCondition allBreakpoints = new CompoundStopCondition();
         LineBreakpoint mainBreakpoint = new LineBreakpoint(main.getPositionInfo().getFileName(), 9, -1, main, envMain.getBuilder().getProof(), "z==1", true, true,6,11);
         
         SymbolicExecutionBreakpointStopCondition bc = new SymbolicExecutionBreakpointStopCondition(mainBreakpoint);
         allBreakpoints.addChildren(bc);
         envMain.getProof().getServices().setFactory(createNewProgramVariableCollectorFactory(bc));
         
         stepReturnWithBreakpoints(envMain.getUi(), envMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory, allBreakpoints);
         stepReturnWithBreakpoints(envMain.getUi(), envMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory, allBreakpoints); 
         
         
         //Test method somethingMain()
         envSomethingMain = createSymbolicExecutionEnvironment(testCaseDirectory, javaPathInkeyRepDirectory, containerTypeName, "somethingMain", null, false, false, false, false, false, false, false, false, false, false);
         IProgramMethod something = searchProgramMethod(envSomethingMain.getServices(), containerTypeName, "something");
         IProgramMethod somethingMain = searchProgramMethod(envSomethingMain.getServices(), containerTypeName, "somethingMain");
         allBreakpoints = new CompoundStopCondition();
         LineBreakpoint somethingMainBreakpoint = new LineBreakpoint(somethingMain.getPositionInfo().getFileName(), 15, -1, somethingMain, envSomethingMain.getBuilder().getProof(),"a==2", true, true,13,17);
         LineBreakpoint somethingBreakpoint = new LineBreakpoint(something.getPositionInfo().getFileName(), 20, -1, something, envSomethingMain.getBuilder().getProof(),"b==3", true, true,19,21);
         bc = new SymbolicExecutionBreakpointStopCondition(somethingBreakpoint, somethingMainBreakpoint);
         allBreakpoints.addChildren(bc);
         envSomethingMain.getProof().getServices().setFactory(createNewProgramVariableCollectorFactory(bc));
         assertSetTreeAfterStep(envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory);
         stepReturnWithBreakpoints(envSomethingMain.getUi(), envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory, allBreakpoints);
         stepReturnWithBreakpoints(envSomethingMain.getUi(), envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory, allBreakpoints); 
         stepReturnWithBreakpoints(envSomethingMain.getUi(), envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory, allBreakpoints);
         stepReturnWithBreakpoints(envSomethingMain.getUi(), envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory, allBreakpoints);
         
         //Test method somethingLocalMain()
         envSomethingLocalMain = createSymbolicExecutionEnvironment(testCaseDirectory, javaPathInkeyRepDirectory, containerTypeName, "somethingLocalMain", null, false, false, false, false, false, false, false, false, false, false);
         IProgramMethod somethingLocal = searchProgramMethod(envSomethingLocalMain.getServices(), containerTypeName, "somethingLocal");
         IProgramMethod somethingLocalMain = searchProgramMethod(envSomethingLocalMain.getServices(), containerTypeName, "somethingLocalMain");
         allBreakpoints = new CompoundStopCondition();
         LineBreakpoint somethingLocalBreakpoint = new LineBreakpoint(somethingLocal.getPositionInfo().getFileName(), 31, -1, somethingLocal, envSomethingLocalMain.getBuilder().getProof(),"y==42*42&&x==42", true, true,29,32);
         LineBreakpoint somethingLocalMainBreakpoint = new LineBreakpoint(somethingLocalMain.getPositionInfo().getFileName(), 26, -1, somethingLocalMain, envSomethingLocalMain.getBuilder().getProof(),"x==42*42&&y==42", true, true,23,27);
         bc = new SymbolicExecutionBreakpointStopCondition(somethingLocalBreakpoint, somethingLocalMainBreakpoint);
         allBreakpoints.addChildren(bc);
         envSomethingLocalMain.getProof().getServices().setFactory(createNewProgramVariableCollectorFactory(bc));
         
         assertSetTreeAfterStep(envSomethingLocalMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory);
         stepReturnWithBreakpoints(envSomethingLocalMain.getUi(), envSomethingLocalMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory, allBreakpoints);
         stepReturnWithBreakpoints(envSomethingLocalMain.getUi(), envSomethingLocalMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory, allBreakpoints); 
         stepReturnWithBreakpoints(envSomethingLocalMain.getUi(), envSomethingLocalMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory, allBreakpoints);
      }
      finally {
         setOneStepSimplificationEnabled(null, originalOneStepSimplification);
         restoreTacletOptions(originalTacletOptions);
         if(envMain!=null){
            envMain.dispose();
         }
         if(envSomethingMain!=null){
            envSomethingMain.dispose();
         }
         if(envSomethingLocalMain!=null){
            envSomethingLocalMain.dispose();
         }
      }
   }
}