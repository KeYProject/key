package de.uka.ilkd.key.smt;

import junit.framework.TestCase;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

public class SMTBeautifierTest extends TestCase {

    public void testSMTBeautifier() throws IOException {

        // Todo Use Files.readString in Java11
        String smt = new String(Files.readAllBytes(Paths.get("/tmp", "a.smt2")));
        System.out.println(SMTBeautifier.indent(smt));

    }
}