package de.uka.ilkd.key.symbolic_execution.strategy;

import java.io.IOException;
import java.util.HashMap;

import javax.xml.parsers.ParserConfigurationException;

import org.xml.sax.SAXException;

import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class TestMethodBreakpointWithConditions extends AbstractSymbolicExecutionTestCase {
   public void testBreakpointStopCondition() throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      SymbolicExecutionEnvironment<CustomConsoleUserInterface> envMain=null;
      SymbolicExecutionEnvironment<CustomConsoleUserInterface> envSomethingMain=null;
      SymbolicExecutionEnvironment<CustomConsoleUserInterface> envSomethingLocalMain=null;
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
         envMain = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, null, false, false, false, false, false, false);
         // Make sure that initial tree is valid
         int oracleIndex = 0;
         assertSetTreeAfterStep(envMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
         IProgramMethod main = searchProgramMethod(envMain.getServices(), "SimpleConditionExample", "main");
         // Test  method main()
         CompoundStopCondition allBreakpoints = new CompoundStopCondition();
         MethodBreakpointStopCondition mainBreakpoint = new MethodBreakpointStopCondition(main.getPositionInfo().getFileName(), 6, -1, main, envMain.getBuilder().getProof(), "z==-1", true, true,6,11,true,true);
         
         allBreakpoints.addChildren(mainBreakpoint);
         envMain.getProof().getServices().setFactory(createNewProgramVariableCollectorFactory(allBreakpoints));
         
         stepReturnWithBreakpoints(envMain.getUi(), envMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(envMain.getUi(), envMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints); 
         
         
         //Test method somethingMain()
         envSomethingMain = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, "somethingMain", null, false, false, false, false, false, false);
         IProgramMethod something = searchProgramMethod(envSomethingMain.getServices(), "SimpleConditionExample", "something");
         IProgramMethod somethingMain = searchProgramMethod(envSomethingMain.getServices(), "SimpleConditionExample", "somethingMain");
         allBreakpoints = new CompoundStopCondition();
         MethodBreakpointStopCondition somethingMainBreakpoint = new MethodBreakpointStopCondition(somethingMain.getPositionInfo().getFileName(), 13, -1, somethingMain, envSomethingMain.getBuilder().getProof(),"a==2", true, true,13,17,true, true);
         MethodBreakpointStopCondition somethingBreakpoint = new MethodBreakpointStopCondition(something.getPositionInfo().getFileName(), 19, -1, something, envSomethingMain.getBuilder().getProof(),"b==3", true, true,19,21,true,true);
         allBreakpoints.addChildren(somethingBreakpoint, somethingMainBreakpoint);
         envSomethingMain.getProof().getServices().setFactory(createNewProgramVariableCollectorFactory(allBreakpoints));
         assertSetTreeAfterStep(envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
         stepReturnWithBreakpoints(envSomethingMain.getUi(), envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(envSomethingMain.getUi(), envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints); 
         stepReturnWithBreakpoints(envSomethingMain.getUi(), envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(envSomethingMain.getUi(), envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         
         //Test method somethingLocalMain()
         envSomethingLocalMain = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, "somethingLocalMain", null, false, false, false, false, false, false);
         IProgramMethod somethingLocal = searchProgramMethod(envSomethingLocalMain.getServices(), "SimpleConditionExample", "somethingLocal");
         IProgramMethod somethingLocalMain = searchProgramMethod(envSomethingLocalMain.getServices(), "SimpleConditionExample", "somethingLocalMain");
         allBreakpoints = new CompoundStopCondition();
         MethodBreakpointStopCondition somethingLocalBreakpoint = new MethodBreakpointStopCondition(somethingLocal.getPositionInfo().getFileName(), 30, -1, somethingLocal, envSomethingLocalMain.getBuilder().getProof(),"y==42*42||x==42", true, true,30,34,true,true);
         MethodBreakpointStopCondition somethingLocalMainBreakpoint = new MethodBreakpointStopCondition(somethingLocalMain.getPositionInfo().getFileName(), 23, -1, somethingLocalMain, envSomethingLocalMain.getBuilder().getProof(),"x==42*42", true, true,23,28,true,true);
         allBreakpoints.addChildren(somethingLocalBreakpoint, somethingLocalMainBreakpoint);
         envSomethingLocalMain.getProof().getServices().setFactory(createNewProgramVariableCollectorFactory(allBreakpoints));
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
