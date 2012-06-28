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
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessStartNode;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessStatement;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessTermination;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessVariable;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * Tests {@link ExecutionNodeWriter} and {@link ExecutionNodeReader}
 * @author Martin Hentschel
 */
public class TestExecutionNodeWriterAndReader extends TestCase {
   /**
    * Tests the reading and writing process without variables.
    */
   public void testWritingAndReading_withoutVariables() throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      doTestWritingAndReading(false);
   }

   /**
    * Tests the reading and writing process.
    */
   public void testWritingAndReading() throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      doTestWritingAndReading(true);
   }
   
   /**
    * Executes the test steps of {@link #testWritingAndReading()} and
    * {@link #testWritingAndReading_withoutVariables()}.
    * @param saveVariabes Save variables?
    */
   protected void doTestWritingAndReading(boolean saveVariabes) throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      // Create model
      IExecutionNode expectedNode = createModel();
      // Serialize model to XML string
      ExecutionNodeWriter writer = new ExecutionNodeWriter();
      String xml = writer.toXML(expectedNode, ExecutionNodeWriter.DEFAULT_ENCODING, saveVariabes);
      // Read from XML string
      ExecutionNodeReader reader = new ExecutionNodeReader();
      IExecutionNode currentNode = reader.read(new ByteArrayInputStream(xml.getBytes(Charset.forName(ExecutionNodeWriter.DEFAULT_ENCODING))));
      TestSymbolicExecutionTreeBuilder.assertExecutionNodes(expectedNode, currentNode, saveVariabes, true);
      // Serialize model to output stream
      ByteArrayOutputStream out = new ByteArrayOutputStream();
      writer.write(expectedNode, ExecutionNodeWriter.DEFAULT_ENCODING, out, saveVariabes);
      // Read from input stream
      currentNode = reader.read(new ByteArrayInputStream(out.toByteArray()));
      TestSymbolicExecutionTreeBuilder.assertExecutionNodes(expectedNode, currentNode, saveVariabes, true);
      // Serialize model to temporary file
      File tempFile = File.createTempFile("TestExecutionNodeWriterAndReader", "testWritingAndReading");
      try {
         tempFile.delete();
         writer.write(expectedNode, ExecutionNodeWriter.DEFAULT_ENCODING, tempFile, saveVariabes);
         assertTrue(tempFile.isFile());
         // Read from tempoary file
         currentNode = reader.read(tempFile);
         TestSymbolicExecutionTreeBuilder.assertExecutionNodes(expectedNode, currentNode, saveVariabes, true);
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
      KeYlessBranchCondition bc = new KeYlessBranchCondition(root, "bc", "pc2", false, "condition of bc");
      root.addChild(bc);
      KeYlessTermination ttrue = new KeYlessTermination(root, "t true", "pc3", true, false);
      root.addChild(ttrue);
      KeYlessTermination tfalse = new KeYlessTermination(root, "t false", "pc4", false, true);
      root.addChild(tfalse);
      KeYlessBranchNode bn = new KeYlessBranchNode(root, "bn", "pc5", true);
      root.addChild(bn);
      KeYlessVariable bnVar1 = new KeYlessVariable(null, true, 2, "myType", "myValue", "bnVar1");
      bn.addVariable(bnVar1);
      KeYlessVariable bnVar2 = new KeYlessVariable(null, false, -1, "myTypeAgain", "myValueAgain", "bnVar2");
      bn.addVariable(bnVar2);
      KeYlessLoopNode ln = new KeYlessLoopNode(root, "ln", "pc6", true);
      root.addChild(ln);
      KeYlessLoopCondition lc = new KeYlessLoopCondition(ln, "lc", "pc7", false);
      ln.addChild(lc);
      KeYlessMethodCall mc = new KeYlessMethodCall(ln, "mc", "pc8", false);
      ln.addChild(mc);
      KeYlessMethodReturn mr = new KeYlessMethodReturn(mc, "mr", "pc9", true, "mc with return value");
      mc.addChild(mr);
      KeYlessStatement s = new KeYlessStatement(root, "s", "pc10", true);
      root.addChild(s);
      KeYlessVariable sVar1 = new KeYlessVariable(null, true, 2, "myType", "myValue", "sVar1");
      s.addVariable(sVar1);
      KeYlessVariable sVar1_1 = new KeYlessVariable(sVar1, true, 2, "myType", "myValue", "sVar1_1");
      sVar1.addChildVariable(sVar1_1);
      KeYlessVariable sVar1_1_1 = new KeYlessVariable(sVar1_1, true, 2, "myType", "myValue", "sVar1_1_1");
      sVar1_1.addChildVariable(sVar1_1_1);
      KeYlessVariable sVar1_2 = new KeYlessVariable(sVar1, true, 2, "myType", "myValue", "sVar1_2");
      sVar1.addChildVariable(sVar1_2);
      KeYlessVariable sVar1_2_1 = new KeYlessVariable(sVar1_2, true, 2, "myType", "myValue", "sVar1_2_1");
      sVar1_2.addChildVariable(sVar1_2_1);
      KeYlessVariable sVar1_2_2 = new KeYlessVariable(sVar1_2, true, 2, "myType", "myValue", "sVar1_2_2");
      sVar1_2.addChildVariable(sVar1_2_2);
      return root;
   }
}
