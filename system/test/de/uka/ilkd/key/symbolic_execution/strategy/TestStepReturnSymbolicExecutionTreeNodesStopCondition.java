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

package de.uka.ilkd.key.symbolic_execution.strategy;

import java.io.IOException;
import java.util.HashMap;

import javax.xml.parsers.ParserConfigurationException;

import org.xml.sax.SAXException;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;

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
      SymbolicExecutionEnvironment<CustomUserInterface> env = null;
      boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
      // Define test settings
      String javaPathInkeyRepDirectory = "examples/_testcase/set/stepReturnTest/test/StepReturnTest.java";
      String containerTypeName = "StepReturnTest";
      final String methodFullName = "main";
      String oraclePathInkeyRepDirectoryFile = "examples/_testcase/set/stepReturnTest/oracle/StepReturnTest";
      String oracleFileExtension = ".xml";
      try {
         originalTacletOptions = setDefaultTacletOptions(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName);
         setOneStepSimplificationEnabled(null, true);
         // Create proof environment for symbolic execution
         env = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, null, false, false, false, false, false, false, false);
         // Make sure that initial tree is valid
         int oracleIndex = 0;
         assertSetTreeAfterStep(env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory);
         // Do steps
         stepInto(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory); // call main
         stepInto(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory); // first level
         stepInto(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory); // call first level
         stepInto(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory); // second level
         stepInto(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory); // call second level
         stepInto(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory); // third level
         stepInto(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory); // call third level
         stepInto(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory); // fourth level
         stepInto(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory); // call fourth level
         stepReturn(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory); // a = a * 2
         stepReturn(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory); // second level
         stepReturn(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory); // first level
         stepReturn(env.getUi(), env.getBuilder(), oraclePathInkeyRepDirectoryFile, ++oracleIndex, oracleFileExtension, keyRepDirectory); // end
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