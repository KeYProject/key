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

/**
 * Tests for {@link LineBreakpointStopCondition}. Tests if execution stops at {@link JavaLineBreakpoint} correctly.
 * 
 * @author Marco Drebing
 */
public class TestLineBreakpointStopConditionSimpleWithHitCount extends AbstractSymbolicExecutionTestCase {


   public void testBreakpointStopCondition() throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      SymbolicExecutionEnvironment<CustomConsoleUserInterface> env=null;
      try{
      // Define test settings
         String javaPathInkeyRepDirectory = "examples/_testcase/set/lineBreakpointsWithHitcountTest/test/BreakpointStopCallerAndLoop.java";
         String containerTypeName = "BreakpointStopCallerAndLoop";
         final String methodFullName = "main";
         String oraclePathInkeyRepDirectoryFile = "examples/_testcase/set/lineBreakpointsWithHitcountTest/oracle/BreakpointStop";
         String oracleFileExtension = ".xml";
         // Create proof environment for symbolic execution
         env = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, null, false, false, false, false, false, false);
         // Make sure that initial tree is valid
         int oracleIndex = 0;
         assertSetTreeAfterStep(env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
         IProgramMethod callerMain=null;
         IProgramMethod calleeMain=null;
         IProgramMethod callerLoop=null;
         for ( KeYJavaType kjt : env.getProof().getJavaInfo().getAllKeYJavaTypes()){
            for(IProgramMethod pm : env.getProof().getJavaInfo().getAllProgramMethods(kjt)){
               if(pm.getFullName().equals("main")&&pm.getBody().getParentClass().equals(keyRepDirectory+"\\examples\\_testcase\\set\\lineBreakpointsWithHitcountTest\\test\\BreakpointStopCallerAndLoop.java")){
                  callerMain = pm;
               }else if(pm.getFullName().equals("main")&&pm.getBody().getParentClass().equals(keyRepDirectory+"\\examples\\_testcase\\set\\lineBreakpointsWithHitcountTest\\test\\BreakpointStopCallee.java")){
                  calleeMain = pm;
               }else if(pm.getFullName().equals("loop")&&pm.getBody().getParentClass().equals(keyRepDirectory+"\\examples\\_testcase\\set\\lineBreakpointsWithHitcountTest\\test\\BreakpointStopCallerAndLoop.java")){
                  callerLoop = pm;
               }
            } 
         }
         CompoundStopCondition allBreakpoints = new CompoundStopCondition();
         LineBreakpointStopCondition firstBreakpoint = new LineBreakpointStopCondition(keyRepDirectory+"\\examples\\_testcase\\set\\lineBreakpointsWithHitcountTest\\test\\BreakpointStopCallerAndLoop.java", 16, -1, callerMain, env.getBuilder().getProof(),null, true, false, 15, 21);
         LineBreakpointStopCondition secondBreakpoint = new LineBreakpointStopCondition(keyRepDirectory+"\\examples\\_testcase\\set\\lineBreakpointsWithHitcountTest\\test\\BreakpointStopCallerAndLoop.java", 10, 2, callerLoop, env.getBuilder().getProof(),null, true, false, 8, 13);
         LineBreakpointStopCondition thirdBreakpoint = new LineBreakpointStopCondition(keyRepDirectory+"\\examples\\_testcase\\set\\lineBreakpointsWithHitcountTest\\test\\BreakpointStopCallee.java", 7, -1, calleeMain, env.getBuilder().getProof(),null, true, false, 6, 9);
         allBreakpoints.addChildren(firstBreakpoint,secondBreakpoint,thirdBreakpoint);
         env.getProof().getServices().setFactory(createNewProgramVariableCollectorFactory(allBreakpoints));
         // Do steps
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
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
