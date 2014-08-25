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

public class TestMethodBreakpointWithConditions extends AbstractSymbolicExecutionTestCase {
   public void testBreakpointStopCondition() throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      SymbolicExecutionEnvironment<CustomUserInterface> envMain=null;
      SymbolicExecutionEnvironment<CustomUserInterface> envSomethingMain=null;
      SymbolicExecutionEnvironment<CustomUserInterface> envSomethingLocalMain=null;
      HashMap<String, String> originalTacletOptions = null;
      boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
      try{
         // Define test settings
         String javaPathInkeyRepDirectory = "examples/_testcase/set/methodBreakpointsWithConditionsTest/test/SimpleConditionExample.java";
         String containerTypeName = "SimpleConditionExample";
         final String methodFullName = "main";
         String oraclePathInkeyRepDirectoryFile = "examples/_testcase/set/methodBreakpointsWithConditionsTest/oracle/BreakpointStopConditionWithCondition";
         String oracleFileExtension = ".xml";
         // Store original settings of KeY
         originalTacletOptions = setDefaultTacletOptions(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName);
         setOneStepSimplificationEnabled(null, true);
         // Create proof environment for symbolic execution
         envMain = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, null, false, false, false, false, false, false, false);
         // Make sure that initial tree is valid
         int oracleIndex = 0;
         assertSetTreeAfterStep(envMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
         IProgramMethod main = searchProgramMethod(envMain.getServices(), "SimpleConditionExample", "main");
         // Test  method main()
         CompoundStopCondition allBreakpoints = new CompoundStopCondition();
         MethodBreakpoint mainBreakpoint = new MethodBreakpoint(main.getPositionInfo().getFileName(), 6, -1, main, envMain.getBuilder().getProof(), "z==-1", true, true,6,11,true,true);
         
         SymbolicExecutionBreakpointStopCondition bc = new SymbolicExecutionBreakpointStopCondition(mainBreakpoint);
         allBreakpoints.addChildren(bc);
         envMain.getProof().getServices().setFactory(createNewProgramVariableCollectorFactory(bc));
         
         stepReturnWithBreakpoints(envMain.getUi(), envMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(envMain.getUi(), envMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints); 
         
         
         //Test method somethingMain()
         envSomethingMain = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, "somethingMain", null, false, false, false, false, false, false, false);
         IProgramMethod something = searchProgramMethod(envSomethingMain.getServices(), "SimpleConditionExample", "something");
         IProgramMethod somethingMain = searchProgramMethod(envSomethingMain.getServices(), "SimpleConditionExample", "somethingMain");
         allBreakpoints = new CompoundStopCondition();
         MethodBreakpoint somethingMainBreakpoint = new MethodBreakpoint(somethingMain.getPositionInfo().getFileName(), 13, -1, somethingMain, envSomethingMain.getBuilder().getProof(),"a==2", true, true,13,17,true, true);
         MethodBreakpoint somethingBreakpoint = new MethodBreakpoint(something.getPositionInfo().getFileName(), 19, -1, something, envSomethingMain.getBuilder().getProof(),"b==3", true, true,19,21,true,true);
         bc = new SymbolicExecutionBreakpointStopCondition(somethingBreakpoint, somethingMainBreakpoint);
         allBreakpoints.addChildren(bc);
         envSomethingMain.getProof().getServices().setFactory(createNewProgramVariableCollectorFactory(bc));
         assertSetTreeAfterStep(envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
         stepReturnWithBreakpoints(envSomethingMain.getUi(), envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(envSomethingMain.getUi(), envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints); 
         stepReturnWithBreakpoints(envSomethingMain.getUi(), envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(envSomethingMain.getUi(), envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         
         //Test method somethingLocalMain()
         envSomethingLocalMain = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, "somethingLocalMain", null, false, false, false, false, false, false, false);
         IProgramMethod somethingLocal = searchProgramMethod(envSomethingLocalMain.getServices(), "SimpleConditionExample", "somethingLocal");
         IProgramMethod somethingLocalMain = searchProgramMethod(envSomethingLocalMain.getServices(), "SimpleConditionExample", "somethingLocalMain");
         allBreakpoints = new CompoundStopCondition();
         MethodBreakpoint somethingLocalBreakpoint = new MethodBreakpoint(somethingLocal.getPositionInfo().getFileName(), 30, -1, somethingLocal, envSomethingLocalMain.getBuilder().getProof(),"y==42*42||x==42", true, true,30,34,true,true);
         MethodBreakpoint somethingLocalMainBreakpoint = new MethodBreakpoint(somethingLocalMain.getPositionInfo().getFileName(), 23, -1, somethingLocalMain, envSomethingLocalMain.getBuilder().getProof(),"x==42*42", true, true,23,28,true,true);
         bc = new SymbolicExecutionBreakpointStopCondition(somethingLocalBreakpoint, somethingLocalMainBreakpoint);
         allBreakpoints.addChildren(bc);
         envSomethingLocalMain.getProof().getServices().setFactory(createNewProgramVariableCollectorFactory(bc));
         assertSetTreeAfterStep(envSomethingLocalMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
         stepReturnWithBreakpoints(envSomethingLocalMain.getUi(), envSomethingLocalMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(envSomethingLocalMain.getUi(), envSomethingLocalMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints); 
         stepReturnWithBreakpoints(envSomethingLocalMain.getUi(), envSomethingLocalMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(envSomethingLocalMain.getUi(), envSomethingLocalMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints); 
         stepReturnWithBreakpoints(envSomethingLocalMain.getUi(), envSomethingLocalMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints); 
      }
      finally{
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