package de.uka.ilkd.key.symbolic_execution.strategy;

import java.io.IOException;

import javax.xml.parsers.ParserConfigurationException;

import org.eclipse.core.runtime.Path;
import org.xml.sax.SAXException;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * Tests for {@link LineBreakpointStopCondition}. Tests if execution stops at {@link JavaLineBreakpoint} correctly.
 * 
 * @author Marco Drebing
 */
public class TestBreakpointStopCondition extends AbstractSymbolicExecutionTestCase {
   /**
    * Does some step over tests on two branches with different number
    * of symbolic execution tree nodes to make sure that the
    * stop conditions works correctly in combination with the goal chooser.
    */
   public void testBreakpointStopCondition() throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      // Define test settings
      String javaPathInkeyRepDirectory = "examples/_testcase/set/lineBreakpointsWithHitcountTest/test/BreakpointStopCallerAndLoop.java";
      String containerTypeName = "BreakpointStopCallerAndLoop";
      final String methodFullName = "main";
      String oraclePathInkeyRepDirectoryFile = "examples/_testcase/set/lineBreakpointsWithHitcountTest/oracle/BreakpointStop";
      String oracleFileExtension = ".xml";
      // Create proof environment for symbolic execution
      SymbolicExecutionEnvironment<CustomConsoleUserInterface> env = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, null, false, false, false);
      // Make sure that initial tree is valid
      int oracleIndex = 0;
      assertSetTreeAfterStep(env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
      IProgramMethod callerMain=null;
      IProgramMethod calleeMain=null;
      IProgramMethod callerLoop=null;
      
      
      for ( KeYJavaType kjt : env.getProof().getJavaInfo().getAllKeYJavaTypes()){
         for(IProgramMethod pm : env.getProof().getJavaInfo().getAllProgramMethods(kjt)){
            if(pm.getFullName().equals("main")&&pm.getBody().getParentClass().equals("C:/bp/key/examples/_testcase/set/lineBreakpointsWithHitcountTest/test/BreakpointStopCallerAndLoop.java")){
               callerMain = pm;
            }else if(pm.getFullName().equals("main")&&pm.getBody().getParentClass().equals("C:/bp/key/examples/_testcase/set/lineBreakpointsWithHitcountTest/test/BreakpointStopCallee.java")){
               calleeMain = pm;
            }else if(pm.getFullName().equals("loop")&&pm.getBody().getParentClass().equals("C:/bp/key/examples/_testcase/set/lineBreakpointsWithHitcountTest/test/BreakpointStopCallerAndLoop.java")){
               calleeMain = pm;
            }
         } 
      }
      
      LineBreakpointStopCondition firstBreakpoint = new LineBreakpointStopCondition(new Path("C:/bp/key/examples/_testcase/set/lineBreakpointsWithHitcountTest/test/BreakpointStopCallerAndLoop.java"), 16, -1, env, callerMain, null, true, false);
      LineBreakpointStopCondition secondBreakpoint = new LineBreakpointStopCondition(new Path("C:/bp/key/examples/_testcase/set/lineBreakpointsWithHitcountTest/test/BreakpointStopCallerAndLoop.java"), 10, 2, env, callerLoop, null, true, false);
      LineBreakpointStopCondition thirdBreakpoint = new LineBreakpointStopCondition(new Path("C:/bp/key/examples/_testcase/set/lineBreakpointsWithHitcountTest/test/BreakpointStopCallee.java"), 7, -1, env, calleeMain, null, true, false);
      CompoundStopCondition allBreakpoints = new CompoundStopCondition(firstBreakpoint,secondBreakpoint,thirdBreakpoint);
      // Do steps
      stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
      stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
      stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
      stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
      stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
      stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
      stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);      

   }
   
}
