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

public class TestLineBreakpointStopConditionSimpleWithConditions extends
      AbstractSymbolicExecutionTestCase {

   
   public void testBreakpointStopCondition() throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      SymbolicExecutionEnvironment<CustomConsoleUserInterface> envMain=null;
      SymbolicExecutionEnvironment<CustomConsoleUserInterface> envSomethingMain=null;
      SymbolicExecutionEnvironment<CustomConsoleUserInterface> envSomethingLocalMain=null;
      try{
      // Define test settings
         String javaPathInkeyRepDirectory = "examples/_testcase/set/lineBreakpointsWithConditionsTest/test/SimpleConditionExample.java";
         String containerTypeName = "SimpleConditionExample";
         final String methodFullName = "main";
         String oraclePathInkeyRepDirectoryFile = "examples/_testcase/set/lineBreakpointsWithConditionsTest/oracle/BreakpointStopConditionWithCondition";
         String oracleFileExtension = ".xml";
         // Create proof environment for symbolic execution
         envMain = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, null, false, false, false, false, false);
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
         LineBreakpointStopCondition mainBreakpoint = new LineBreakpointStopCondition(keyRepDirectory+"\\examples\\_testcase\\set\\lineBreakpointsWithConditionsTest\\test\\SimpleConditionExample.java", 9, -1, main, envMain.getBuilder().getProof(), "z==1", true, true,6,11);
         
         allBreakpoints.addChildren(mainBreakpoint);
         envMain.getProof().getServices().setFactory(createNewProgramVariableCollectorFactory(allBreakpoints));
         
         stepReturnWithBreakpoints(envMain.getUi(), envMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(envMain.getUi(), envMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints); 
         
         
         //Test method somethingMain()
         envSomethingMain = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, "somethingMain", null, false, false, false, false, false);
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
         LineBreakpointStopCondition somethingMainBreakpoint = new LineBreakpointStopCondition(keyRepDirectory+"\\examples\\_testcase\\set\\lineBreakpointsWithConditionsTest\\test\\SimpleConditionExample.java", 15, -1, somethingMain, envSomethingMain.getBuilder().getProof(),"a==2", true, true,13,17);
         LineBreakpointStopCondition somethingBreakpoint = new LineBreakpointStopCondition(keyRepDirectory+"\\examples\\_testcase\\set\\lineBreakpointsWithConditionsTest\\test\\SimpleConditionExample.java", 20, -1, something, envSomethingMain.getBuilder().getProof(),"b==3", true, true,19,21);
         allBreakpoints.addChildren(somethingBreakpoint, somethingMainBreakpoint);
         envSomethingMain.getProof().getServices().setFactory(createNewProgramVariableCollectorFactory(allBreakpoints));
         assertSetTreeAfterStep(envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
         stepReturnWithBreakpoints(envSomethingMain.getUi(), envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(envSomethingMain.getUi(), envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints); 
         stepReturnWithBreakpoints(envSomethingMain.getUi(), envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(envSomethingMain.getUi(), envSomethingMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         
         //Test method somethingLocalMain()
         envSomethingLocalMain = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, "somethingLocalMain", null, false, false, false, false, false);
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
         LineBreakpointStopCondition somethingLocalBreakpoint = new LineBreakpointStopCondition(keyRepDirectory+"\\examples\\_testcase\\set\\lineBreakpointsWithConditionsTest\\test\\SimpleConditionExample.java", 31, -1, somethingLocal, envSomethingLocalMain.getBuilder().getProof(),"y==42*42&&x==42", true, true,29,32);
         LineBreakpointStopCondition somethingLocalMainBreakpoint = new LineBreakpointStopCondition(keyRepDirectory+"\\examples\\_testcase\\set\\lineBreakpointsWithConditionsTest\\test\\SimpleConditionExample.java", 26, -1, somethingLocalMain, envSomethingLocalMain.getBuilder().getProof(),"x==42*42&&y==42", true, true,23,27);
         allBreakpoints.addChildren(somethingLocalBreakpoint, somethingLocalMainBreakpoint);
         envSomethingLocalMain.getProof().getServices().setFactory(createNewProgramVariableCollectorFactory(allBreakpoints));
         
         assertSetTreeAfterStep(envSomethingLocalMain.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
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
