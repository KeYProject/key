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
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * Tests {@link ExecutionNodeWriter} and {@link ExecutionNodeReader}
 * @author Martin Hentschel
 */
public class TestExecutionNodeWriterAndReader extends TestCase {
   /**
    * Tests the reading and writing process.
    */
   public void testWritingAndReading() throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      // Create model
      IExecutionNode expectedNode = createModel();
      // Serialize model to XML string
      ExecutionNodeWriter writer = new ExecutionNodeWriter();
      String xml = writer.toXML(expectedNode, ExecutionNodeWriter.DEFAULT_ENCODING);
      // Read from XML string
      ExecutionNodeReader reader = new ExecutionNodeReader();
      IExecutionNode currentNode = reader.read(new ByteArrayInputStream(xml.getBytes(Charset.forName(ExecutionNodeWriter.DEFAULT_ENCODING))));
      TestSymbolicExecutionTreeBuilder.assertExecutionNodes(expectedNode, currentNode);
      // Serialize model to output stream
      ByteArrayOutputStream out = new ByteArrayOutputStream();
      writer.write(expectedNode, ExecutionNodeWriter.DEFAULT_ENCODING, out);
      // Read from input stream
      currentNode = reader.read(new ByteArrayInputStream(out.toByteArray()));
      TestSymbolicExecutionTreeBuilder.assertExecutionNodes(expectedNode, currentNode);
      // Serialize model to temporary file
      File tempFile = File.createTempFile("TestExecutionNodeWriterAndReader", "testWritingAndReading");
      try {
         tempFile.delete();
         writer.write(expectedNode, ExecutionNodeWriter.DEFAULT_ENCODING, tempFile);
         assertTrue(tempFile.isFile());
         // Read from tempoary file
         currentNode = reader.read(tempFile);
         TestSymbolicExecutionTreeBuilder.assertExecutionNodes(expectedNode, currentNode);
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
      KeYlessStartNode root = new KeYlessStartNode("start");
      KeYlessBranchCondition bc = new KeYlessBranchCondition(root, "bc");
      root.addChild(bc);
      KeYlessTermination ttrue = new KeYlessTermination(root, "t true", true);
      root.addChild(ttrue);
      KeYlessTermination tfalse = new KeYlessTermination(root, "t false", false);
      root.addChild(tfalse);
      KeYlessBranchNode bn = new KeYlessBranchNode(root, "bn");
      root.addChild(bn);
      KeYlessLoopNode ln = new KeYlessLoopNode(root, "ln");
      root.addChild(ln);
      KeYlessLoopCondition lc = new KeYlessLoopCondition(ln, "lc");
      ln.addChild(lc);
      KeYlessMethodCall mc = new KeYlessMethodCall(ln, "mc");
      ln.addChild(mc);
      KeYlessMethodReturn mr = new KeYlessMethodReturn(mc, "mr", "mc with return value");
      mc.addChild(mr);
      KeYlessStatement s = new KeYlessStatement(root, "s");
      root.addChild(s);
      return root;
   }
}
