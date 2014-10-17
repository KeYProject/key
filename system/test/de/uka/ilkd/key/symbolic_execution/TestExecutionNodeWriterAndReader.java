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

package de.uka.ilkd.key.symbolic_execution;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.nio.charset.Charset;

import javax.xml.parsers.ParserConfigurationException;

import junit.framework.TestCase;

import org.xml.sax.SAXException;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessBranchCondition;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessBranchStatement;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessConstraint;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessExceptionalMethodReturn;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessLoopCondition;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessLoopInvariant;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessLoopStatement;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessMethodCall;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessMethodReturn;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessMethodReturnValue;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessOperationContract;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessStart;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessStatement;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessTermination;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessValue;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessVariable;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination.TerminationKind;

/**
 * Tests {@link ExecutionNodeWriter} and {@link ExecutionNodeReader}
 * @author Martin Hentschel
 */
public class TestExecutionNodeWriterAndReader extends TestCase {
   /**
    * Tests the reading and writing process without variables and without call stack.
    */
   public void testWritingAndReading_withoutVariables_and_withoutCallStack_withReturnValues() throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      doTestWritingAndReading(false, false, true, true);
   }
   
   /**
    * Tests the reading and writing process without call stack.
    */
   public void testWritingAndReading_withoutCallStack_withReturnValues() throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      doTestWritingAndReading(true, false, true, true);
   }
   
   /**
    * Tests the reading and writing process without variables.
    */
   public void testWritingAndReading_withoutVariables_withReturnValues() throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      doTestWritingAndReading(false, true, true, true);
   }

   /**
    * Tests the reading and writing process.
    */
   public void testWritingAndReading_withReturnValues() throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      doTestWritingAndReading(true, true, true, true);
   }
   
   /**
    * Tests the reading and writing process without variables and without call stack.
    */
   public void testWritingAndReading_withoutVariables_and_withoutCallStack_noReturnValues() throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      doTestWritingAndReading(false, false, false, true);
   }
   
   /**
    * Tests the reading and writing process without call stack.
    */
   public void testWritingAndReading_withoutCallStack_noReturnValues() throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      doTestWritingAndReading(true, false, false, false);
   }
   
   /**
    * Tests the reading and writing process without variables.
    */
   public void testWritingAndReading_withoutVariables_noReturnValues() throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      doTestWritingAndReading(false, true, false, true);
   }

   /**
    * Tests the reading and writing process.
    */
   public void testWritingAndReading_noReturnValues() throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      doTestWritingAndReading(true, true, false, false);
   }
   
   /**
    * Executes the test steps of {@link #testWritingAndReading()},
    * {@link #testWritingAndReading_withoutVariables()},
    * {@link #testWritingAndReading_withoutCallStack()} and
    * {@link #testWritingAndReading_withoutVariables_and_withoutCallStack()}.
    * @param saveVariabes Save variables?
    * @param saveCallStack Save call stack?
    * @param saveReturnValues Save method return values?
    * @param saveConstraints Save constraints?
    */
   protected void doTestWritingAndReading(boolean saveVariabes, 
                                          boolean saveCallStack,
                                          boolean saveReturnValues,
                                          boolean saveConstraints) throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      // Create model
      IExecutionNode<?> expectedNode = createModel();
      // Serialize model to XML string
      ExecutionNodeWriter writer = new ExecutionNodeWriter();
      String xml = writer.toXML(expectedNode, ExecutionNodeWriter.DEFAULT_ENCODING, saveVariabes, saveCallStack, saveReturnValues, saveConstraints);
      // Read from XML string
      ExecutionNodeReader reader = new ExecutionNodeReader();
      IExecutionNode<?> currentNode = reader.read(new ByteArrayInputStream(xml.getBytes(Charset.forName(ExecutionNodeWriter.DEFAULT_ENCODING))));
      TestSymbolicExecutionTreeBuilder.assertExecutionNodes(expectedNode, currentNode, saveVariabes, saveCallStack, true, saveReturnValues, saveConstraints);
      // Serialize model to output stream
      ByteArrayOutputStream out = new ByteArrayOutputStream();
      writer.write(expectedNode, ExecutionNodeWriter.DEFAULT_ENCODING, out, saveVariabes, saveCallStack, saveReturnValues, saveConstraints);
      // Read from input stream
      currentNode = reader.read(new ByteArrayInputStream(out.toByteArray()));
      TestSymbolicExecutionTreeBuilder.assertExecutionNodes(expectedNode, currentNode, saveVariabes, saveCallStack, true, saveReturnValues, saveConstraints);
      // Serialize model to temporary file
      File tempFile = File.createTempFile("TestExecutionNodeWriterAndReader", "testWritingAndReading");
      try {
         tempFile.delete();
         writer.write(expectedNode, ExecutionNodeWriter.DEFAULT_ENCODING, tempFile, saveVariabes, saveCallStack, saveReturnValues, saveConstraints);
         assertTrue(tempFile.isFile());
         // Read from temporary file
         currentNode = reader.read(tempFile);
         TestSymbolicExecutionTreeBuilder.assertExecutionNodes(expectedNode, currentNode, saveVariabes, saveCallStack, true, saveReturnValues, saveConstraints);
      }
      finally {
         tempFile.delete();
      }
   }
   
   /**
    * Creates an example symbolic execution tree.
    * @return The root of the example symbolic execution tree.
    */
   protected IExecutionNode<?> createModel() {
      KeYlessStart root = new KeYlessStart("start", "pc1", true);
      root.addCallStackEntry(root);
      KeYlessBranchCondition bc = new KeYlessBranchCondition(root, "bc", "pc2", false, "condition of bc", true, true, "myCustomBC");
      bc.addCallStackEntry(root);
      bc.addCallStackEntry(bc);
      root.addChild(bc);
      KeYlessTermination tNormal = new KeYlessTermination(root, "t normal", "pc3", true, TerminationKind.NORMAL, true);
      root.addChild(tNormal);
      root.addTermination(tNormal);
      KeYlessTermination tExceptional = new KeYlessTermination(root, "t exceptional", "pc4", false, TerminationKind.EXCEPTIONAL, false);
      root.addChild(tExceptional);
      root.addTermination(tExceptional);
      KeYlessTermination tloop = new KeYlessTermination(root, "t loop", "pcLoopTermination", false, TerminationKind.LOOP_BODY, true);
      root.addChild(tloop);
      root.addTermination(tloop);
      KeYlessBranchStatement bn = new KeYlessBranchStatement(root, "bn", "pc5", true, true);
      bn.addCallStackEntry(root);
      bn.addCallStackEntry(bc);
      root.addChild(bn);
      IExecutionConstraint constraint = new KeYlessConstraint("myConstraint");
      bn.addConstraint(constraint);
      KeYlessVariable bnVar1 = new KeYlessVariable(null, true, 2, "bnVar1");
      bn.addVariable(bnVar1);
      KeYlessValue bnVar1Value1 = new KeYlessValue(bnVar1, "myType1", "myValue1", "value of bnVar1", true, false, "c1");
      bnVar1.addValue(bnVar1Value1);
      bnVar1Value1.addConstraint(new KeYlessConstraint("constraint of bnVar1"));
      KeYlessValue bnVar1Value2 = new KeYlessValue(bnVar1, "myType2", "myValue2", "value of bnVar1", false, true, "c2");
      bnVar1.addValue(bnVar1Value2);
      KeYlessVariable bnVar2 = new KeYlessVariable(null, false, -1, "bnVar2");
      bn.addVariable(bnVar2);
      KeYlessValue bnVar2Value = new KeYlessValue(bnVar2, "myTypeAgain", "myValueAgain", "value of bnVar2", false, true, "c3");
      bnVar2.addValue(bnVar2Value);
      KeYlessLoopStatement ln = new KeYlessLoopStatement(root, "ln", "pc6", true, false);
      root.addChild(ln);
      ln.addCompletedBlock(bn, "My Block Completion Condition!");
      bn.addBlockCompletion(ln);
      KeYlessLoopCondition lc = new KeYlessLoopCondition(ln, "lc", "pc7", false, true);
      ln.addChild(lc);
      KeYlessMethodCall mc = new KeYlessMethodCall(ln, "mc", "pc8", false);
      mc.addCallStackEntry(mc);
      ln.addChild(mc);
      KeYlessMethodReturn mr = new KeYlessMethodReturn(mc, "mr", "pc9", true, "mc with return value", "mc(arg)", "mc(arg) with return value", true, "myMethodReturnCondition");
      mr.addReturnValue(new KeYlessMethodReturnValue("rv1", "rv1String", false, null));
      mr.addReturnValue(new KeYlessMethodReturnValue("rv2", "rv2String", true, "c2String"));
      mr.addCallStackEntry(mc);
      mc.addChild(mr);
      mc.addMethodReturn(mr);
      
      KeYlessVariable mrVar1 = new KeYlessVariable(null, true, 2, "mrVar1");
      mr.addCallStateVariable(mrVar1);
      KeYlessValue mrVar1Value1 = new KeYlessValue(mrVar1, "myType1", "myValue1", "value of mrVar1", true, false, "c1");
      mrVar1.addValue(mrVar1Value1);
      KeYlessVariable mrVar1child1 = new KeYlessVariable(mrVar1Value1, true, 2, "mrVar1child1");
      mrVar1Value1.addChildVariable(mrVar1child1);
      KeYlessValue mrVar1child1Value1 = new KeYlessValue(mrVar1child1, "myType2", "myValue1child1", "value of mrVar1child1", true, false, "c2");
      mrVar1child1.addValue(mrVar1child1Value1);
      
      KeYlessExceptionalMethodReturn emr = new KeYlessExceptionalMethodReturn(mc, "emr", "pcExceptional", true, "mc(arg)", "myExceptionalMethodReturnCondition");
      emr.addCallStackEntry(mc);
      mc.addChild(emr);
      mc.addMethodReturn(emr);
      KeYlessOperationContract contract = new KeYlessOperationContract(root, "useOperationContract", "pcUse", true, false, true, false, "ResultTerm", "ExceptionTerm", "SelfTerm", "ParamA, ParamB");
      root.addChild(contract);
      KeYlessLoopInvariant invariant = new KeYlessLoopInvariant(root, "useLoppInvariant", "pcUseLoopInvariant", false, true);
      root.addChild(invariant);
      KeYlessStatement s = new KeYlessStatement(root, "s", "pc10", true);
      root.addChild(s);
      KeYlessVariable sVar1 = new KeYlessVariable(null, true, 2, "sVar1");
      s.addVariable(sVar1);
      KeYlessValue sVar1Value = new KeYlessValue(sVar1, "myType", "myValue", "value of sVar1", false, false, "c4");
      sVar1.addValue(sVar1Value);
      KeYlessVariable sVar1_1 = new KeYlessVariable(sVar1Value, true, 2, "sVar1_1");
      sVar1Value.addChildVariable(sVar1_1);
      KeYlessValue sVar1_1Value = new KeYlessValue(sVar1_1, "myType", "myValue", "value of sVar1_1", true, true, "c5");
      sVar1_1.addValue(sVar1_1Value);
      KeYlessVariable sVar1_1_1 = new KeYlessVariable(sVar1_1Value, true, 1, "sVar1_1_1");
      sVar1_1Value.addChildVariable(sVar1_1_1);
      KeYlessValue sVar1_1_1Value = new KeYlessValue(sVar1_1_1, "myType", "myValue", "value of sVar1_1_1", true, false, "c6");
      sVar1_1_1.addValue(sVar1_1_1Value);
      KeYlessVariable sVar1_2 = new KeYlessVariable(sVar1Value, true, 2, "sVar1_2");
      sVar1Value.addChildVariable(sVar1_2);
      KeYlessValue sVar1_2Value = new KeYlessValue(sVar1_2, "myType", "myValue", "value of sVar1_2", false, true, "c7");
      sVar1_2.addValue(sVar1_2Value);
      KeYlessVariable sVar1_2_1 = new KeYlessVariable(sVar1_2Value, true, 2, "sVar1_2_1");
      sVar1_2Value.addChildVariable(sVar1_2_1);
      KeYlessValue sVar1_2_1Value = new KeYlessValue(sVar1_2_1, "myType", "myValue", "value of sVar1_2_1", false, false, "c8");
      sVar1_2_1.addValue(sVar1_2_1Value);
      KeYlessVariable sVar1_2_2 = new KeYlessVariable(sVar1_2Value, true, 2, "sVar1_2_2");
      sVar1_2Value.addChildVariable(sVar1_2_2);
      KeYlessValue sVar1_2_2Value = new KeYlessValue(sVar1_2_2, "myType", "myValue", "value of sVar1_2_2", true, true, "c9");
      sVar1_2_2.addValue(sVar1_2_2Value);
      return root;
   }
}