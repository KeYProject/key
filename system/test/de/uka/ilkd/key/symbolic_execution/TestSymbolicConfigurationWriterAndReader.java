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

import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.SymbolicConfigurationReader.KeYlessAssociation;
import de.uka.ilkd.key.symbolic_execution.SymbolicConfigurationReader.KeYlessEquivalenceClass;
import de.uka.ilkd.key.symbolic_execution.SymbolicConfigurationReader.KeYlessConfiguration;
import de.uka.ilkd.key.symbolic_execution.SymbolicConfigurationReader.KeYlessObject;
import de.uka.ilkd.key.symbolic_execution.SymbolicConfigurationReader.KeYlessState;
import de.uka.ilkd.key.symbolic_execution.SymbolicConfigurationReader.KeYlessValue;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicConfiguration;

/**
 * Tests {@link SymbolicConfigurationWriter} and {@link SymbolicConfigurationReader}
 * @author Martin Hentschel
 */
public class TestSymbolicConfigurationWriterAndReader extends TestCase {
   /**
    * Tests the writing and reading of an {@link ISymbolicConfiguration}.
    */
   public void testWritingAndReading() throws ProofInputException, ParserConfigurationException, SAXException, IOException {
      // Create model
      ISymbolicConfiguration expectedNode = createModel();
      // Serialize model to XML string
      SymbolicConfigurationWriter writer = new SymbolicConfigurationWriter();
      String xml = writer.toXML(expectedNode, ExecutionNodeWriter.DEFAULT_ENCODING);
      // Read from XML string
      SymbolicConfigurationReader reader = new SymbolicConfigurationReader();
      ISymbolicConfiguration currentNode = reader.read(new ByteArrayInputStream(xml.getBytes(Charset.forName(ExecutionNodeWriter.DEFAULT_ENCODING))));
      TestSymbolicConfigurationExtractor.assertModel(expectedNode, currentNode);
      // Serialize model to output stream
      ByteArrayOutputStream out = new ByteArrayOutputStream();
      writer.write(expectedNode, ExecutionNodeWriter.DEFAULT_ENCODING, out);
      // Read from input stream
      currentNode = reader.read(new ByteArrayInputStream(out.toByteArray()));
      TestSymbolicConfigurationExtractor.assertModel(expectedNode, currentNode);
      // Serialize model to temporary file
      File tempFile = File.createTempFile("TestExecutionNodeWriterAndReader", "testWritingAndReading");
      try {
         tempFile.delete();
         writer.write(expectedNode, ExecutionNodeWriter.DEFAULT_ENCODING, tempFile);
         assertTrue(tempFile.isFile());
         // Read from temporary file
         currentNode = reader.read(tempFile);
         TestSymbolicConfigurationExtractor.assertModel(expectedNode, currentNode);
      }
      finally {
         tempFile.delete();
      }
   }

   /**
    * Creates an example model.
    * @return The root of the example model.
    */
   protected ISymbolicConfiguration createModel() {
      KeYlessConfiguration model = new KeYlessConfiguration();
      model.addEquivalenceClass(new KeYlessEquivalenceClass(ImmutableSLList.<String>nil().append("A", "B", "C"), "A"));
      model.addEquivalenceClass(new KeYlessEquivalenceClass(ImmutableSLList.<String>nil().append("1", "2", "3"), "63"));
      // state
      KeYlessState state = new KeYlessState("exampleState");
      state.addValue(new KeYlessValue("v1", "v1", false, -1, "v1Value", "t1", null));
      state.addValue(new KeYlessValue("v2", "v2", false, -1, "v2Value", "t2", "c1"));
      model.setState(state);
      // o1
      KeYlessObject o1 = new KeYlessObject("o1", "t1");
      o1.addValue(new KeYlessValue("o1", "o1", false, -1, "o1Value", "t1", "c2"));
      model.addObject(o1);
      // o2
      KeYlessObject o2 = new KeYlessObject("o2", "t2");
      model.addObject(o2);
      // o3
      KeYlessObject o3 = new KeYlessObject("o3", "t3");
      o3.addValue(new KeYlessValue("o1", "o1", false, -1, "o1Value", "t1", null));
      o3.addValue(new KeYlessValue("o2", "o2", true, 52, "o2Value", "t2", "c3"));
      o3.addValue(new KeYlessValue("o3", "o3", false, -1, "o3Value", "t3", null));
      model.addObject(o3);
      // associations
      state.addAssociation(new KeYlessAssociation("a1", "a1", false, -1, o2, null));
      o1.addAssociation(new KeYlessAssociation("a1", "a1", false, -1, o1, "c4"));
      o1.addAssociation(new KeYlessAssociation("a1", "a1", false, -1, o2, "c5"));
      o2.addAssociation(new KeYlessAssociation("a1", "a1", false, -1, o3, null));
      o3.addAssociation(new KeYlessAssociation("a1", "a1", false, -1, o1, "c6"));
      return model;
   }
}