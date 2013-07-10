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

public class TestMethodBreakpointWithHitCount extends
      AbstractSymbolicExecutionTestCase {
   public void testBreakpointStopCondition() throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      SymbolicExecutionEnvironment<CustomConsoleUserInterface> env=null;
      try{
         // Define test settings
         String javaPathInkeyRepDirectory = "examples/_testcase/set/methodBreakpointsWithHitcountTest/test/BreakpointStopCallerAndLoop.java";
         String containerTypeName = "BreakpointStopCallerAndLoop";
         final String methodFullName = "main";
         String oraclePathInkeyRepDirectoryFile = "examples/_testcase/set/methodBreakpointsWithHitcountTest/oracle/MethodBreakpointStop";
         String oracleFileExtension = ".xml";
         // Create proof environment for symbolic execution
         env = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, null, false, false, false, false);
         // Make sure that initial tree is valid
         int oracleIndex = 0;
         assertSetTreeAfterStep(env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
         IProgramMethod callerMain=null;
         IProgramMethod calleeMain=null;
         IProgramMethod callerLoop=null;
         for ( KeYJavaType kjt : env.getProof().getJavaInfo().getAllKeYJavaTypes()){
            for(IProgramMethod pm : env.getProof().getJavaInfo().getAllProgramMethods(kjt)){
               if(pm.getFullName().equals("main")&&pm.getBody().getParentClass().equals(keyRepDirectory+"\\examples\\_testcase\\set\\methodBreakpointsWithHitcountTest\\test\\BreakpointStopCallerAndLoop.java")){
                  callerMain = pm;
               }else if(pm.getFullName().equals("main")&&pm.getBody().getParentClass().equals(keyRepDirectory+"\\examples\\_testcase\\set\\methodBreakpointsWithHitcountTest\\test\\BreakpointStopCallee.java")){
                  calleeMain = pm;
               }else if(pm.getFullName().equals("loop")&&pm.getBody().getParentClass().equals(keyRepDirectory+"\\examples\\_testcase\\set\\methodBreakpointsWithHitcountTest\\test\\BreakpointStopCallerAndLoop.java")){
                  callerLoop = pm;
               }
            } 
         }
         CompoundStopCondition allBreakpoints = new CompoundStopCondition();
         //on method call and return
         MethodBreakpointStopCondition inAndOutBreakpoint = new MethodBreakpointStopCondition(keyRepDirectory+"\\examples\\_testcase\\set\\methodBreakpointsWithHitcountTest\\test\\BreakpointStopCallerAndLoop.java", 15, -1, env, callerMain, env.getBuilder().getProof(), allBreakpoints, null, true, false, 15, 24,true,true);
         //on method call with hitcount
         MethodBreakpointStopCondition hitCountBreakpoint = new MethodBreakpointStopCondition(keyRepDirectory+"\\examples\\_testcase\\set\\methodBreakpointsWithHitcountTest\\test\\BreakpointStopCallerAndLoop.java", 8, 2, env, callerLoop, env.getBuilder().getProof(), allBreakpoints, null, true, false, 8, 13, true, false);
         //on method return with hitcount
         MethodBreakpointStopCondition thirdBreakpoint = new MethodBreakpointStopCondition(keyRepDirectory+"\\examples\\_testcase\\set\\methodBreakpointsWithHitcountTest\\test\\BreakpointStopCallerAndLoop.java", 6, 2, env, calleeMain, env.getBuilder().getProof(), allBreakpoints, null, true, false, 6, 9, false, true);
         allBreakpoints.addChildren(inAndOutBreakpoint,hitCountBreakpoint,thirdBreakpoint);
         // Do steps
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);     

      }finally{
         if(env!=null){
            env.dispose();
         }
      }
   }
}
