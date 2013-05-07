package de.uka.ilkd.key.symbolic_execution.strategy;

import java.io.File;
import java.io.IOException;

import javax.xml.parsers.ParserConfigurationException;

import org.eclipse.core.runtime.Path;
import org.xml.sax.SAXException;

import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.strategy.LineBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
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
      
      // Do steps
      stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
      stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
      stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
      stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
      stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
      stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
      stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);        

   }
   
   
   /**
    * Executes an "step return" global on all goals on the given {@link SymbolicExecutionTreeBuilder}.
    * @param ui The {@link CustomConsoleUserInterface} to use.
    * @param builder The {@link SymbolicExecutionGoalChooser} to do step on.
    * @param oraclePathInBaseDirFile The oracle path.
    * @param oracleIndex The index of the current step.
    * @param oracleFileExtension The oracle file extension
    * @param baseDir The base directory for oracles.
    * @throws IOException Occurred Exception
    * @throws ProofInputException Occurred Exception
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    */
   protected static void stepReturnWithBreakpoints(CustomConsoleUserInterface ui, 
                                    SymbolicExecutionTreeBuilder builder, 
                                    String oraclePathInBaseDirFile, 
                                    int oracleIndex, 
                                    String oracleFileExtension, 
                                    File baseDir) throws IOException, ProofInputException, ParserConfigurationException, SAXException {
      // Set stop condition to stop after a number of detected symbolic execution tree nodes instead of applied rules
      Proof proof = builder.getProof();
      CompoundStopCondition stopCondition = new CompoundStopCondition();
      LineBreakpointStopCondition firstBreakpoint = new LineBreakpointStopCondition(new Path("C:/bp/key/examples/_testcase/set/lineBreakpointsWithHitcountTest/test/BreakpointStopCallerAndLoop.java"), 16, -1, "", true);
      LineBreakpointStopCondition secondBreakpoint = new LineBreakpointStopCondition(new Path("C:/bp/key/examples/_testcase/set/lineBreakpointsWithHitcountTest/test/BreakpointStopCallerAndLoop.java"), 10, 2, "", true);
      LineBreakpointStopCondition thirdBreakpoint = new LineBreakpointStopCondition(new Path("C:/bp/key/examples/_testcase/set/lineBreakpointsWithHitcountTest/test/BreakpointStopCallee.java"), 7, -1, "", true);
      CompoundStopCondition allBreakpoints = new CompoundStopCondition(firstBreakpoint,secondBreakpoint,thirdBreakpoint);
      stopCondition.addChildren(new ExecutedSymbolicExecutionTreeNodesStopCondition(ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN));
      stopCondition.addChildren(new StepReturnSymbolicExecutionTreeNodesStopCondition());
      stopCondition.addChildren(allBreakpoints);
      proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(stopCondition);
      // Run proof
      SymbolicExecutionUtil.updateStrategyPropertiesForSymbolicExecution(proof);
      ui.startAndWaitForAutoMode(proof);
      // Update symbolic execution tree 
      builder.analyse();
      // Test result
      assertSetTreeAfterStep(builder, oraclePathInBaseDirFile, oracleIndex, oracleFileExtension, baseDir);
   }
}
