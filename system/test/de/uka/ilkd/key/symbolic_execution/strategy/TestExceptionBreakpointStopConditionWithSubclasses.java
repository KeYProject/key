package de.uka.ilkd.key.symbolic_execution.strategy;

import java.io.IOException;

import javax.xml.parsers.ParserConfigurationException;

import org.xml.sax.SAXException;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class TestExceptionBreakpointStopConditionWithSubclasses extends
      AbstractSymbolicExecutionTestCase {


   public void testBreakpointStopCondition() throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      String originalRuntimeExceptions = null;
      SymbolicExecutionEnvironment<CustomConsoleUserInterface> env = null;
      try {
         // Define test settings
         String javaPathInkeyRepDirectory = "examples/_testcase/set/exceptionBreakpointsWithSubclassesTest/test/ClassCastAndNullpointerExceptions.java";
         String containerTypeName = "ClassCastAndNullpointerExceptions";
         final String methodFullName = "main";
         String oraclePathInkeyRepDirectoryFile = "examples/_testcase/set/exceptionBreakpointsWithSubclassesTest/oracle/ClassCastAndNullpointerExceptions";
         String oracleFileExtension = ".xml";
         // Store original settings of KeY which requires that at least one proof was instantiated.
         if (!SymbolicExecutionUtil.isChoiceSettingInitialised()) {
            env = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, null, false, false, false, false);
            env.dispose();
         }
         originalRuntimeExceptions = SymbolicExecutionUtil.getChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS);
         assertNotNull(originalRuntimeExceptions);
         SymbolicExecutionUtil.setChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW);
         // Create proof environment for symbolic execution
         env = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, null, false, false, false, false);
         // Make sure that initial tree is valid
         int oracleIndex = 0;
         assertSetTreeAfterStep(env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
         CompoundStopCondition allBreakpoints = new CompoundStopCondition();
         
         Proof proof = env.getBuilder().getProof();
         StrategyProperties props = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
         props.put(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_EXPAND);
         props.put(StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_EXPAND);
         proof.getSettings().getStrategySettings().setActiveStrategyProperties(props);
         
         ExceptionBreakpointStopCondition firstBreakpoint = new ExceptionBreakpointStopCondition(env, "java.lang.Exception", true, true, true, true, -1);
         allBreakpoints.addChildren(firstBreakpoint);
         // Do steps
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
         stepReturnWithBreakpoints(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory, allBreakpoints);
      }
      finally {
         // Restore runtime option
         if (originalRuntimeExceptions != null) {
            SymbolicExecutionUtil.setChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, originalRuntimeExceptions);
         }
         if (env != null) {
            env.dispose();
         }
      }
   }
}
