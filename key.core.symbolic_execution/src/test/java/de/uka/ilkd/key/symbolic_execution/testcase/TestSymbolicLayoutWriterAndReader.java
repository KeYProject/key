/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.testcase;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.nio.charset.Charset;
import javax.xml.parsers.ParserConfigurationException;

import de.uka.ilkd.key.symbolic_execution.ExecutionNodeWriter;
import de.uka.ilkd.key.symbolic_execution.SymbolicLayoutReader;
import de.uka.ilkd.key.symbolic_execution.SymbolicLayoutReader.*;
import de.uka.ilkd.key.symbolic_execution.SymbolicLayoutWriter;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicLayout;

import org.key_project.util.collection.ImmutableSLList;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.xml.sax.SAXException;

/**
 * Tests {@link SymbolicLayoutWriter} and {@link SymbolicLayoutReader}
 *
 * @author Martin Hentschel
 */
public class TestSymbolicLayoutWriterAndReader {
    /**
     * Tests the writing and reading of an {@link ISymbolicLayout}.
     */
    @Test
    public void testWritingAndReading()
            throws ParserConfigurationException, SAXException, IOException {
        // Create model
        ISymbolicLayout expectedNode = createModel();
        // Serialize model to XML string
        SymbolicLayoutWriter writer = new SymbolicLayoutWriter();
        String xml = writer.toXML(expectedNode, ExecutionNodeWriter.DEFAULT_ENCODING);
        // Read from XML string
        SymbolicLayoutReader reader = new SymbolicLayoutReader();
        ISymbolicLayout currentNode = reader.read(new ByteArrayInputStream(
            xml.getBytes(Charset.forName(ExecutionNodeWriter.DEFAULT_ENCODING))));
        TestSymbolicLayoutExtractor.assertModel(expectedNode, currentNode);
        // Serialize model to output stream
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        writer.write(expectedNode, ExecutionNodeWriter.DEFAULT_ENCODING, out);
        // Read from input stream
        currentNode = reader.read(new ByteArrayInputStream(out.toByteArray()));
        TestSymbolicLayoutExtractor.assertModel(expectedNode, currentNode);
        // Serialize model to temporary file
        File tempFile =
            File.createTempFile("TestExecutionNodeWriterAndReader", "testWritingAndReading");
        try {
            tempFile.delete();
            writer.write(expectedNode, ExecutionNodeWriter.DEFAULT_ENCODING, tempFile);
            Assertions.assertTrue(tempFile.isFile());
            // Read from temporary file
            currentNode = reader.read(tempFile);
            TestSymbolicLayoutExtractor.assertModel(expectedNode, currentNode);
        } finally {
            tempFile.delete();
        }
    }

    /**
     * Creates an example model.
     *
     * @return The root of the example model.
     */
    protected ISymbolicLayout createModel() {
        KeYlessLayout model = new KeYlessLayout();
        model.addEquivalenceClass(
            new KeYlessEquivalenceClass(ImmutableSLList.<String>nil().append("A", "B", "C"), "A"));
        model.addEquivalenceClass(
            new KeYlessEquivalenceClass(ImmutableSLList.<String>nil().append("1", "2", "3"), "63"));
        // state
        KeYlessState state = new KeYlessState("exampleState");
        state.addValue(new KeYlessValue("v1", "v1", false, "-1", "v1Value", "t1", null));
        state.addValue(new KeYlessValue("v2", "v2", false, "-1", "v2Value", "t2", "c1"));
        model.setState(state);
        // o1
        KeYlessObject o1 = new KeYlessObject("o1", "t1");
        o1.addValue(new KeYlessValue("o1", "o1", false, "-1", "o1Value", "t1", "c2"));
        model.addObject(o1);
        // o2
        KeYlessObject o2 = new KeYlessObject("o2", "t2");
        model.addObject(o2);
        // o3
        KeYlessObject o3 = new KeYlessObject("o3", "t3");
        o3.addValue(new KeYlessValue("o1", "o1", false, "-1", "o1Value", "t1", null));
        o3.addValue(new KeYlessValue("o2", "o2", true, "52", "o2Value", "t2", "c3"));
        o3.addValue(new KeYlessValue("o3", "o3", false, "-1", "o3Value", "t3", null));
        model.addObject(o3);
        // associations
        state.addAssociation(new KeYlessAssociation("a1", "a1", false, "-1", o2, null));
        o1.addAssociation(new KeYlessAssociation("a1", "a1", false, "-1", o1, "c4"));
        o1.addAssociation(new KeYlessAssociation("a1", "a1", false, "-1", o2, "c5"));
        o2.addAssociation(new KeYlessAssociation("a1", "a1", false, "-1", o3, null));
        o3.addAssociation(new KeYlessAssociation("a1", "a1", false, "-1", o1, "c6"));
        return model;
    }
}
