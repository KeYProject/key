package de.uka.ilkd.key.symbolic_execution.strategy;

import java.io.IOException;

import javax.xml.parsers.ParserConfigurationException;

import org.xml.sax.SAXException;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class TestJavaWatchpointStopConditionWithHitCount extends
      AbstractSymbolicExecutionTestCase {


   public void testBreakpointStopCondition() throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      SymbolicExecutionEnvironment<CustomConsoleUserInterface> env=null;
      try{
         // Define test settings
         String javaPathInkeyRepDirectory = "examples/_testcase/set/javaWatchpointsWithHitCountTest/test/GlobalAccessesAndModifications.java";
         String containerTypeName = "GlobalAccessesAndModifications";
         final String methodFullName = "main";
         String oraclePathInkeyRepDirectoryFile = "examples/_testcase/set/javaWatchpointsWithHitCountTest/oracle/GlobalAccessesAndModifications";
         String oracleFileExtension = ".xml";
         // Create proof environment for symbolic execution
         env = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, null, false, false, false, false);
         // Make sure that initial tree is valid
         int oracleIndex = 0;
         assertSetTreeAfterStep(env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
         CompoundStopCondition allBreakpoints = new CompoundStopCondition();
         KeYJavaType containerType = null;
         for ( KeYJavaType kjt : env.getProof().getJavaInfo().getAllKeYJavaTypes()){
            if(kjt.getSort().toString().equals("GlobalAccessesAndModifications")){
               containerType = kjt;
            }
         }
         
         JavaWatchpointStopCondition firstBreakpoint = new JavaWatchpointStopCondition(true, 2, "access", true,false, containerType, env.getBuilder().getProof());
         JavaWatchpointStopCondition secondBreakpoint = new JavaWatchpointStopCondition(true, -1, "modification", false,true, containerType, env.getBuilder().getProof());
         JavaWatchpointStopCondition thirdBreakpoint = new JavaWatchpointStopCondition(true, 2, "accessAndModification", true,true, containerType, env.getBuilder().getProof());
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
