// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
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
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessBranchNode;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessLoopCondition;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessLoopNode;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessMethodCall;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessMethodReturn;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessMethodReturnValue;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessStartNode;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessStatement;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessTermination;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessUseLoopInvariant;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessUseOperationContract;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessValue;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessVariable;
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
      doTestWritingAndReading(false, false, true);
   }
   
   /**
    * Tests the reading and writing process without call stack.
    */
   public void testWritingAndReading_withoutCallStack_withReturnValues() throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      doTestWritingAndReading(true, false, true);
   }
   
   /**
    * Tests the reading and writing process without variables.
    */
   public void testWritingAndReading_withoutVariables_withReturnValues() throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      doTestWritingAndReading(false, true, true);
   }

   /**
    * Tests the reading and writing process.
    */
   public void testWritingAndReading_withReturnValues() throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      doTestWritingAndReading(true, true, true);
   }
   
   /**
    * Tests the reading and writing process without variables and without call stack.
    */
   public void testWritingAndReading_withoutVariables_and_withoutCallStack_noReturnValues() throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      doTestWritingAndReading(false, false, false);
   }
   
   /**
    * Tests the reading and writing process without call stack.
    */
   public void testWritingAndReading_withoutCallStack_noReturnValues() throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      doTestWritingAndReading(true, false, false);
   }
   
   /**
    * Tests the reading and writing process without variables.
    */
   public void testWritingAndReading_withoutVariables_noReturnValues() throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      doTestWritingAndReading(false, true, false);
   }

   /**
    * Tests the reading and writing process.
    */
   public void testWritingAndReading_noReturnValues() throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      doTestWritingAndReading(true, true, false);
   }
   
   /**
    * Executes the test steps of {@link #testWritingAndReading()},
    * {@link #testWritingAndReading_withoutVariables()},
    * {@link #testWritingAndReading_withoutCallStack()} and
    * {@link #testWritingAndReading_withoutVariables_and_withoutCallStack()}.
    * @param saveVariabes Save variables?
    * @param saveCallStack Save call stack?
    * @param saveReturnValues Save method return values?
    */
   protected void doTestWritingAndReading(boolean saveVariabes, 
                                          boolean saveCallStack,
                                          boolean saveReturnValues) throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      // Create model
      IExecutionNode expectedNode = createModel();
      // Serialize model to XML string
      ExecutionNodeWriter writer = new ExecutionNodeWriter();
      String xml = writer.toXML(expectedNode, ExecutionNodeWriter.DEFAULT_ENCODING, saveVariabes, saveCallStack, saveReturnValues);
      // Read from XML string
      ExecutionNodeReader reader = new ExecutionNodeReader();
      IExecutionNode currentNode = reader.read(new ByteArrayInputStream(xml.getBytes(Charset.forName(ExecutionNodeWriter.DEFAULT_ENCODING))));
      TestSymbolicExecutionTreeBuilder.assertExecutionNodes(expectedNode, currentNode, saveVariabes, saveCallStack, true, saveReturnValues);
      // Serialize model to output stream
      ByteArrayOutputStream out = new ByteArrayOutputStream();
      writer.write(expectedNode, ExecutionNodeWriter.DEFAULT_ENCODING, out, saveVariabes, saveCallStack, saveReturnValues);
      // Read from input stream
      currentNode = reader.read(new ByteArrayInputStream(out.toByteArray()));
      TestSymbolicExecutionTreeBuilder.assertExecutionNodes(expectedNode, currentNode, saveVariabes, saveCallStack, true, saveReturnValues);
      // Serialize model to temporary file
      File tempFile = File.createTempFile("TestExecutionNodeWriterAndReader", "testWritingAndReading");
      try {
         tempFile.delete();
         writer.write(expectedNode, ExecutionNodeWriter.DEFAULT_ENCODING, tempFile, saveVariabes, saveCallStack, saveReturnValues);
         assertTrue(tempFile.isFile());
         // Read from tempoary file
         currentNode = reader.read(tempFile);
         TestSymbolicExecutionTreeBuilder.assertExecutionNodes(expectedNode, currentNode, saveVariabes, saveCallStack, true, saveReturnValues);
      }
      finally {
         tempFile.delete();
      }
   }
   
   /**
    * Creates an example symbolic execution tree.
    * @return The root of the example symbolic execution tree.
    */
   protected IExecutionNode createModel() {
      KeYlessStartNode root = new KeYlessStartNode("start", "pc1", true);
      root.addCallStackEntry(root);
      KeYlessBranchCondition bc = new KeYlessBranchCondition(root, "bc", "pc2", false, "condition of bc", true, true, "myCustomBC");
      bc.addCallStackEntry(root);
      bc.addCallStackEntry(bc);
      root.addChild(bc);
      KeYlessTermination tNormal = new KeYlessTermination(root, "t normal", "pc3", true, TerminationKind.NORMAL);
      root.addChild(tNormal);
      KeYlessTermination tExceptional = new KeYlessTermination(root, "t exceptional", "pc4", false, TerminationKind.EXCEPTIONAL);
      root.addChild(tExceptional);
      KeYlessTermination tloop = new KeYlessTermination(root, "t loop", "pcLoopTermination", false, TerminationKind.LOOP_BODY);
      root.addChild(tloop);
      KeYlessBranchNode bn = new KeYlessBranchNode(root, "bn", "pc5", true);
      bn.addCallStackEntry(root);
      bn.addCallStackEntry(bc);
      root.addChild(bn);
      KeYlessVariable bnVar1 = new KeYlessVariable(null, true, 2, "bnVar1");
      bn.addVariable(bnVar1);
      KeYlessValue bnVar1Value1 = new KeYlessValue(bnVar1, "myType1", "myValue1", "value of bnVar1", true, false, "c1");
      bnVar1.addValue(bnVar1Value1);
      KeYlessValue bnVar1Value2 = new KeYlessValue(bnVar1, "myType2", "myValue2", "value of bnVar1", false, true, "c2");
      bnVar1.addValue(bnVar1Value2);
      KeYlessVariable bnVar2 = new KeYlessVariable(null, false, -1, "bnVar2");
      bn.addVariable(bnVar2);
      KeYlessValue bnVar2Value = new KeYlessValue(bnVar2, "myTypeAgain", "myValueAgain", "value of bnVar2", false, true, "c3");
      bnVar2.addValue(bnVar2Value);
      KeYlessLoopNode ln = new KeYlessLoopNode(root, "ln", "pc6", true);
      root.addChild(ln);
      KeYlessLoopCondition lc = new KeYlessLoopCondition(ln, "lc", "pc7", false);
      ln.addChild(lc);
      KeYlessMethodCall mc = new KeYlessMethodCall(ln, "mc", "pc8", false);
      mc.addCallStackEntry(mc);
      ln.addChild(mc);
      KeYlessMethodReturn mr = new KeYlessMethodReturn(mc, "mr", "pc9", true, "mc with return value", true);
      mr.addReturnValue(new KeYlessMethodReturnValue("rv1", "rv1String", false, null));
      mr.addReturnValue(new KeYlessMethodReturnValue("rv2", "rv2String", true, "c2String"));
      mc.addCallStackEntry(mc);
      mc.addChild(mr);
      KeYlessUseOperationContract useContract = new KeYlessUseOperationContract(root, "useOperationContract", "pcUse", true, false, true, false);
      root.addChild(useContract);
      KeYlessUseLoopInvariant useInvariant = new KeYlessUseLoopInvariant(root, "useLoppInvariant", "pcUseLoopInvariant", false, true);
      root.addChild(useInvariant);
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
