// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.testcase.strategy;

import java.io.IOException;
import java.util.HashMap;

import javax.xml.parsers.ParserConfigurationException;

import org.xml.sax.SAXException;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.StepReturnSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionGoalChooser;
import de.uka.ilkd.key.symbolic_execution.testcase.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;

/**
 * Tests for {@link StepReturnSymbolicExecutionTreeNodesStopCondition} and
 * {@link SymbolicExecutionGoalChooser}. To do a step over the
 * {@link CompoundStopCondition} is also tested.
 * @author Martin Hentschel
 */
public class TestStepReturnSymbolicExecutionTreeNodesStopCondition extends AbstractSymbolicExecutionTestCase {
   /**
    * Does some step return tests on one branch.
    */
   public void testStepReturn() throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      HashMap<String, String> originalTacletOptions = null;
      SymbolicExecutionEnvironment<DefaultUserInterfaceControl> env = null;
      boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
      // Define test settings
      String javaPathInkeyRepDirectory = "/set/stepReturnTest/test/StepReturnTest.java";
      String containerTypeName = "StepReturnTest";
      final String methodFullName = "main";
      String oraclePathInkeyRepDirectoryFile = "/set/stepReturnTest/oracle/StepReturnTest";
      String oracleFileExtension = ".xml";
      try {
         originalTacletOptions = setDefaultTacletOptions(testCaseDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName);
         setOneStepSimplificationEnabled(null, true);
         // Create proof environment for symbolic execution
         env = createSymbolicExecutionEnvironment(testCaseDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, null, false, false, false, false, false, false, false, false, false);
         // Make sure that initial tree is valid
         int oracleIndex = 0;
         assertSetTreeAfterStep(env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory);
         // Do steps
         stepInto(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory); // call main
         stepInto(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory); // first level
         stepInto(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory); // call first level
         stepInto(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory); // second level
         stepInto(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory); // call second level
         stepInto(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory); // third level
         stepInto(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory); // call third level
         stepInto(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory); // fourth level
         stepInto(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory); // call fourth level
         stepReturn(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory); // a = a * 2
         stepReturn(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory); // second level
         stepReturn(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory); // first level
         stepReturn(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, testCaseDirectory); // end
      }
      finally {
         setOneStepSimplificationEnabled(null, originalOneStepSimplification);
         restoreTacletOptions(originalTacletOptions);
         if (env != null) {
            env.dispose();
         }
      }
  }
}