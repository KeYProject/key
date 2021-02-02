package de.uka.ilkd.key.smt;

import junit.framework.TestCase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.key_project.util.Streams;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;

@RunWith(Parameterized.class)
public class SMTBeautifierTest extends TestCase {

    @Parameter(0)
    public String smt;

    @Parameter(1)
    public String expected;

    @Parameters
    public static Object[][] parameters() throws IOException {
        String[] smt = Streams.toString(SMTBeautifierTest.class.getResourceAsStream("beautifier.in.smt2")).split("; *----+");
        String[] expected = Streams.toString(SMTBeautifierTest.class.getResourceAsStream("beautifier.out.smt2")).split("; *----+");
        assertEquals("The two files must have same number of clauses", smt.length, expected.length);
        Object[][] result = new Object[smt.length][];
        for (int i = 0; i < result.length; i++) {
            result[i] = new Object[] { smt[i], expected[i] };
        }
        return result;
    }

    @Test
    public void testSMTBeautifier() throws IOException {
        assertEquals(expected.trim(), SMTBeautifier.indent(smt, 80).trim());
    }

    // revealed bugs!
    @Test
    public void testIdemPotent() throws IOException {
        String result1 = SMTBeautifier.indent(smt, 80).trim();
        String result2 = SMTBeautifier.indent(result1, 80).trim();
        assertEquals(result1, result2);
    }
}