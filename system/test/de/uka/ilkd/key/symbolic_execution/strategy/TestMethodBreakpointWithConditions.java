package de.uka.ilkd.key.symbolic_execution.strategy;

import java.io.IOException;

import javax.xml.parsers.ParserConfigurationException;

import org.xml.sax.SAXException;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class TestMethodBreakpointWithConditions extends
      AbstractSymbolicExecutionTestCase {
   
   public void testBreakpointStopCondition() throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      SymbolicExecutionEnvironment<CustomConsoleUserInterface> envMain=null;
      SymbolicExecutionEnvironment<CustomConsoleUserInterface> envSomethingMain=null;
      SymbolicExecutionEnvironment<CustomConsoleUserInterface> envSomethingLocalMain=null;
      try{
      // Define test settings
         String javaPathInkeyRepDirectory = "examples/_testcase/set/methodBreakpointsWithConditionsTest/test/SimpleConditionExample.java";
         String containerTypeName = "SimpleConditionExample";
         final String methodFullName = "main";
         String oraclePathInkeyRepDirectoryFile = "examples/_testcase/set/methodBreakpointsWithConditionsTest/oracle/BreakpointStopConditionWithCondition";
         String oracleFileExtension = ".xml";
         // Create proof environment for symbolic execution
         envMain = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, null, false, false, false, false);
         // Make sure that initial tree is valid
         int oracleIndex = 0;
         assertSetTreeAfterStep(envMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
         IProgramMethod main=null;
         // Test  method main()
         for ( KeYJavaType kjt : envMain.getProof().getJavaInfo().getAllKeYJavaTypes()){
            for(IProgramMethod pm : envMain.getProof().getJavaInfo().getAllProgramMethods(kjt)){
               if(pm.getFullName().equals("main")){
                  main = pm;
               }
            } 
         }
         CompoundStopCondition allBreakpoints = new CompoundStopCondition();
         MethodBreakpointStopCondition mainBreakpoint = new MethodBreakpointStopCondition(keyRepDirectory+"\\examples\\_testcase\\set\\methodBreakpointsWithConditionsTest\\test\\SimpleConditionExample.java", 6, -1, main, envMain.getBuilder().getProof(),allBreakpoints, "z==-1", true, true,6,11,true,true);
         
         allBreakpoints.addChildren(mainBreakpoint);
         
         stepReturnWithBreakpoints(envMain.getUi(), envMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(envMain.getUi(), envMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints); 
         
         
         //Test method somethingMain()
         envSomethingMain = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, "somethingMain", null, false, false, false, false);
         IProgramMethod something=null;
         IProgramMethod somethingMain=null;
         for ( KeYJavaType kjt : envSomethingMain.getProof().getJavaInfo().getAllKeYJavaTypes()){
            for(IProgramMethod pm : envSomethingMain.getProof().getJavaInfo().getAllProgramMethods(kjt)){
               if(pm.getFullName().equals("something")){
                  something = pm;
               } else if(pm.getFullName().equals("somethingMain")){
                  somethingMain = pm;
               }
            } 
         }
         allBreakpoints = new CompoundStopCondition();
         MethodBreakpointStopCondition somethingMainBreakpoint = new MethodBreakpointStopCondition(keyRepDirectory+"\\examples\\_testcase\\set\\methodBreakpointsWithConditionsTest\\test\\SimpleConditionExample.java", 13, -1, somethingMain, envSomethingMain.getBuilder().getProof(), allBreakpoints, "a==2", true, true,13,17,true, true);
         MethodBreakpointStopCondition somethingBreakpoint = new MethodBreakpointStopCondition(keyRepDirectory+"\\examples\\_testcase\\set\\methodBreakpointsWithConditionsTest\\test\\SimpleConditionExample.java", 19, -1, something, envSomethingMain.getBuilder().getProof(), allBreakpoints, "b==3", true, true,19,21,true,true);
         allBreakpoints.addChildren(somethingBreakpoint, somethingMainBreakpoint);
         assertSetTreeAfterStep(envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
         stepReturnWithBreakpoints(envSomethingMain.getUi(), envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(envSomethingMain.getUi(), envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints); 
         stepReturnWithBreakpoints(envSomethingMain.getUi(), envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(envSomethingMain.getUi(), envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         
         //Test method somethingLocalMain()
         envSomethingLocalMain = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, "somethingLocalMain", null, false, false, false, false);
         IProgramMethod somethingLocal=null;
         IProgramMethod somethingLocalMain=null;
         for ( KeYJavaType kjt : envSomethingLocalMain.getProof().getJavaInfo().getAllKeYJavaTypes()){
            for(IProgramMethod pm : envSomethingLocalMain.getProof().getJavaInfo().getAllProgramMethods(kjt)){
               if(pm.getFullName().equals("somethingLocal")){
                  somethingLocal = pm;
               } else if(pm.getFullName().equals("somethingLocalMain")){
                  somethingLocalMain = pm;
               }
            } 
         }
         allBreakpoints = new CompoundStopCondition();
         MethodBreakpointStopCondition somethingLocalBreakpoint = new MethodBreakpointStopCondition(keyRepDirectory+"\\examples\\_testcase\\set\\methodBreakpointsWithConditionsTest\\test\\SimpleConditionExample.java", 30, -1, somethingLocal, envSomethingLocalMain.getBuilder().getProof(), allBreakpoints, "y==42*42||x==42", true, true,30,34,true,true);
         MethodBreakpointStopCondition somethingLocalMainBreakpoint = new MethodBreakpointStopCondition(keyRepDirectory+"\\examples\\_testcase\\set\\methodBreakpointsWithConditionsTest\\test\\SimpleConditionExample.java", 23, -1, somethingLocalMain, envSomethingLocalMain.getBuilder().getProof(), allBreakpoints, "x==42*42", true, true,23,28,true,true);
         allBreakpoints.addChildren(somethingLocalBreakpoint, somethingLocalMainBreakpoint);
         assertSetTreeAfterStep(envSomethingLocalMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
         stepReturnWithBreakpoints(envSomethingLocalMain.getUi(), envSomethingLocalMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(envSomethingLocalMain.getUi(), envSomethingLocalMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints); 
         stepReturnWithBreakpoints(envSomethingLocalMain.getUi(), envSomethingLocalMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(envSomethingLocalMain.getUi(), envSomethingLocalMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints); 
         stepReturnWithBreakpoints(envSomethingLocalMain.getUi(), envSomethingLocalMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints); 
      }finally{
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
