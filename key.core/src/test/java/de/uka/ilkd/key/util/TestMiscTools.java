/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;


import java.io.*;
import java.net.URL;
import java.net.URLConnection;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;
import java.util.zip.ZipOutputStream;

import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.abstraction.*;
import de.uka.ilkd.key.java.ast.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.ast.statement.SetStatement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.speclang.jml.translation.ProgramVariableCollection;
import de.uka.ilkd.key.speclang.njml.JmlFacade;
import de.uka.ilkd.key.speclang.njml.JmlIO;
import de.uka.ilkd.key.speclang.njml.SpecMathMode;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.IOUtil;

import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import static de.uka.ilkd.key.util.MiscTools.containsWholeWord;
import static de.uka.ilkd.key.util.MiscTools.isJMLComment;
import static org.junit.jupiter.api.Assertions.*;

public class TestMiscTools {

    @Test
    public void testMakeFilenameRelativeUnix() {
        // run only on UNIX-like systems
        if (File.separatorChar != '/') {
            return;
        }

        String s = "/home/daniel/bla";
        String t = "/home/daniel/blubb";
        String u = MiscTools.makeFilenameRelative(s, t);
        assertEquals("../bla", u);
        // s shorter than t
        t = "/home/daniel/bla/foo/bar";
        u = MiscTools.makeFilenameRelative(s, t);
        assertEquals("../..", u);
        // s already relative
        s = s.substring(1);
        assertEquals(s, MiscTools.makeFilenameRelative(s, t));
        s = "/home/../home/daniel/";
        t = "/home";
        assertEquals("daniel", MiscTools.makeFilenameRelative(s, t));
    }

    @Test
    @Disabled("weigl: Disabled b/c failing on Windows Server (Github Action). " +
        "Failing is not  reproducible on Windows.")
    public void testMakeFilenameRelativeWindows() {
        // run only on Windows systems
        if (File.separatorChar != '\\') {
            return;
        }

        // test windows delimiters
        String s = "C:\\Windows";
        String t = "c:\\";
        String u = MiscTools.makeFilenameRelative(s, t);
        assertEquals("Windows", u);
        // do stupid things
        t = File.separator + "home" + File.separator + "daniel";
        u = MiscTools.makeFilenameRelative(s, t);
        assertEquals("..\\..\\Windows", u);
    }

    @Test
    public void testToValidFileName() {
        assertEquals("foo_bar", MiscTools.toValidFileName("foo:bar"));
        assertEquals("foo_bar", MiscTools.toValidFileName("foo\\bar"));
        assertEquals("foo(bar)", MiscTools.toValidFileName("foo[bar]"));
    }

    @Test
    public void testContainsWholeWord() {
        assertTrue(containsWholeWord("foo bar", "foo"));
        assertTrue(containsWholeWord("foo;", "foo"));
        assertTrue(containsWholeWord("\rfoo\t", "foo"));
        assertTrue(containsWholeWord(" foo foo", "foo"));
        assertFalse(containsWholeWord("foobar", "foo"));
        assertFalse(containsWholeWord("bar", "foo"));
    }

    @Test
    public void testIsJMLComment() {
        assertTrue(isJMLComment("/*@iarijagjs"));
        assertTrue(isJMLComment("//@ sasahgue"));
        assertTrue(isJMLComment("//+KeY@"));
        assertTrue(isJMLComment("//-ESC@"));
        assertFalse(isJMLComment("//-KeY@"));
        assertFalse(isJMLComment("// @"));
        assertFalse(isJMLComment("/*"));
        assertFalse(isJMLComment("/**"));
    }

    /**
     * This is a test for the method {@link MiscTools#parseURL(String)}. It tests for some strings
     * if they can be converted to URLs correctly. Note: This test creates a temporary zip file.
     *
     * @throws Exception
     *         if a string can not be converted successfully
     */
    @Test
    public void testTryParseURL() throws Exception {
        // test null string -> MalformedURLException
        try {
            URL uNull = MiscTools.parseURL(null);
            fail("Expected a MalformedURLException!");
        } catch (NullPointerException e) {
            assertEquals("No URL can be created from null!", e.getMessage());
        }

        // test empty string -> URL of user working directory
        URL u0 = MiscTools.parseURL("");
        assertEquals(System.getProperty("user.dir"), Paths.get(u0.toURI()).toString());

        String tmp = System.getProperty("java.io.tmpdir");
        Path p = Paths.get(tmp, "te st.txt");

        // test simple path string without url prefix and encoding
        URL u1 = MiscTools.parseURL(p.toString());
        assertNotNull(u1);

        // test file url string
        String correctURL = p.toUri().toURL().toString();
        URL u2 = MiscTools.parseURL(correctURL);
        assertNotNull(u2);

        // test removal of redundant elements
        Path pRedundant = Paths.get(tmp, ".", ".", "te st.txt");
        URL uRedundant = MiscTools.parseURL(pRedundant.toString());

        // test a special format of string from antlr parser ("URL:<url_string>")
        URL parserURL = MiscTools.parseURL("URL:" + correctURL);

        assertEquals(u1, u2);
        assertEquals(u1, uRedundant);
        assertEquals(u1, parserURL);

        // test http url string
        String correctHttp = "https://www.key-project.org/KEY.cer";
        URL u3 = MiscTools.parseURL(correctHttp);
        assertNotNull(u3);

        // write a test zip file
        byte[] b = "test content".getBytes(StandardCharsets.UTF_8);
        String entryName = "entry with whitespace.txt";
        Path zipP = Files.createTempFile("test with whitespace!", ".zip");
        try (FileOutputStream fos = new FileOutputStream(zipP.toFile());
                ZipOutputStream zos = new ZipOutputStream(fos)) {
            zos.putNextEntry(new ZipEntry(entryName));
            zos.write(b);
        }

        try (ZipFile zf = new ZipFile(zipP.toFile())) {
            URL entryURL = MiscTools.getZipEntryURI(zf, entryName).toURL();
            URLConnection juc = entryURL.openConnection();
            juc.setUseCaches(false);
            try (InputStream is = juc.getInputStream()) {
                assertNotNull(is);
                // try if the file can be read correctly
                assertEquals(new String(b, StandardCharsets.UTF_8), IOUtil.readFrom(is));
            }

            // test reparsing jar url
            URL u4 = MiscTools.parseURL(entryURL.toString());
            assertNotNull(u4);
            assertEquals(entryURL, u4);
        }

        // clean up temporary file
        Files.deleteIfExists(zipP);
    }

    @Test
    public void testLocalOuts() {
        var services = TacletForTests.services().copy(false);
        KeYJavaType intKjt = services.getTypeConverter().getKeYJavaType(PrimitiveType.JAVA_INT);
        var x = new LocationVariable(new ProgramElementName("x"), intKjt);
        var y = new LocationVariable(new ProgramElementName("y"), intKjt);
        var z = new LocationVariable(new ProgramElementName("z"), intKjt);
        var stmt1 = new CopyAssignment(x, y);
        var lexer = JmlFacade.createLexer("set z = 1;");
        var parser = JmlFacade.createParser(lexer);
        var setCtx = parser.set_statement();
        var stmt2 = new SetStatement(new KeyAst.SetStatementContext(setCtx), null);
        var pv = new ProgramVariableCollection();
        var objKjt = services.getJavaInfo().getJavaLangObject();
        var io = new JmlIO(services).classType(objKjt).specMathMode(SpecMathMode.BIGINT);
        var value = io.translateTerm(stmt2.getParserContext().getValue());
        services.getSpecificationRepository().addStatementSpec(stmt2,
            new SpecificationRepository.JmlStatementSpec(pv,
                ImmutableList.of(services.getTermBuilder().var(z), value)));
        var block = new StatementBlock(stmt1, stmt2);
        var outs = MiscTools.getLocalOuts(block, services);
        assertEquals(2, outs.size());
        assertTrue(outs.contains(x));
        assertTrue(outs.contains(z));
    }
}
