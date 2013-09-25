package de.uka.ilkd.key.symbolic_execution.strategy;

import java.io.IOException;

import javax.xml.parsers.ParserConfigurationException;

import org.xml.sax.SAXException;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class TestKeYWatchpointGlobalVariablesOnTrueWithHitCount extends
      AbstractSymbolicExecutionTestCase {


   public void testBreakpointStopCondition() throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      SymbolicExecutionEnvironment<CustomConsoleUserInterface> env=null;
      try{
         // Define test settings
         String javaPathInkeyRepDirectory = "examples/_testcase/set/keyWatchpointGlobalVariablesOnTrueWithHitCount/test/GlobalVariablesOnTrue.java";
         String containerTypeName = "GlobalVariablesOnTrue";
         final String methodFullName = "doSomething";
         String oraclePathInkeyRepDirectoryFile = "examples/_testcase/set/keyWatchpointGlobalVariablesOnTrueWithHitCount/oracle/GlobalVariablesOnTrue";
         String oracleFileExtension = ".xml";
         // Create proof environment for symbolic execution
         env = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, null, false, false, false, false, false);
         // Make sure that initial tree is valid
         int oracleIndex = 0;
         assertSetTreeAfterStep(env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
         CompoundStopCondition allBreakpoints = new CompoundStopCondition();
         JavaInfo javaInfo = env.getServices().getJavaInfo();
         KeYJavaType containerType = javaInfo.getTypeByClassName(containerTypeName);
         
         KeYWatchpointStopCondition globalVariableCondition = new KeYWatchpointStopCondition(2, env.getBuilder().getProof(),"x_global==17", true, true, containerType, true);
         
         allBreakpoints.addChildren(globalVariableCondition);
         env.getProof().getServices().setFactory(createNewProgramVariableCollectorFactory(allBreakpoints));
         // Do steps
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
