package de.uka.ilkd.key.smt.communication;

import junit.framework.TestCase;

import java.io.IOException;
import java.io.StringReader;

public class BufferedMessageReaderTest extends TestCase {

    public void testSplitting() throws IOException {
        BufferedMessageReader r = new BufferedMessageReader(new StringReader("a\nC>C>b\n\nC>c"), new String[] { "C>" } );
        assertEquals("a\n", r.readMessage());
        assertEquals("b\n\n", r.readMessage());
        assertEquals("c", r.readMessage());
        assertEquals("", r.drain());
    }

    public void testEmptyStart() throws IOException {
        String[] delims = { "X", "Y" };
        BufferedMessageReader br = new BufferedMessageReader(new StringReader("XXXaXbYcYXY"), delims);
        assertEquals("a", br.readMessage());
        assertEquals("b", br.readMessage());
        assertEquals("c", br.readMessage());
        assertEquals(null, br.readMessage());
    }

    public void testDrain() throws IOException {
        BufferedMessageReader r = new BufferedMessageReader(new StringReader("a\nC>C>b\n\nC>c"), new String[] { "C>" } );
        assertEquals("a\n", r.readMessage());
        assertEquals("C>b\n\nC>c", r.drain());
    }

    public void testXY() throws IOException {
        String[] delims = { "X", "Y" };
        BufferedMessageReader br = new BufferedMessageReader(new StringReader("aXbYc"), delims);
        assertEquals("a", br.readMessage());
        assertEquals("b", br.readMessage());
        assertEquals("c", br.readMessage());
        assertEquals(null, br.readMessage());
    }

    public void testNewline() throws IOException {
        String[] delims = { "\n", "\r" };
        BufferedMessageReader br = new BufferedMessageReader(new StringReader("a\r\nb\nc"), delims);
        assertEquals("a", br.readMessage());
        assertEquals("b", br.readMessage());
        assertEquals("c", br.readMessage());
        assertEquals(null, br.readMessage());
    }

}
