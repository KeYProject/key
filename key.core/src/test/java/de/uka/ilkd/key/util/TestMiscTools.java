/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;


import java.io.File;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.net.URI;
import java.net.URL;
import java.net.URLConnection;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Optional;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;
import java.util.zip.ZipOutputStream;

import de.uka.ilkd.key.java.recoderext.URLDataLocation;

import org.key_project.util.java.IOUtil;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import recoder.io.ArchiveDataLocation;
import recoder.io.DataFileLocation;
import recoder.io.DataLocation;

import static de.uka.ilkd.key.util.MiscTools.containsWholeWord;
import static de.uka.ilkd.key.util.MiscTools.isJMLComment;
import static org.junit.jupiter.api.Assertions.*;

public class TestMiscTools {

    @Test
    public void testDisectFilenameUnix() {
        // run only on UNIX-like systems
        if (File.separatorChar != '/') {
            return;
        }
        String s = "/home/daniel//workspace/key";
        Object[] ls = MiscTools.disectFilename(s).toArray();
        assertEquals("", ls[0]);
        assertEquals("key", ls[4]);
        s = s.substring(1);
        ls = MiscTools.disectFilename(s).toArray();
        assertEquals("home", ls[0]);
        s = s + "/";
        ls = MiscTools.disectFilename(s).toArray();
        assertEquals(4, ls.length);
        assertEquals("key", ls[3]);
        s = "." + s;
        ls = MiscTools.disectFilename(s).toArray();
        assertEquals(4, ls.length);
        assertEquals("key", ls[3]);
    }

    @Test
    public void testDisectFilenameWindows() {
        // run only on Windows systems
        if (File.separatorChar != '\\') {
            return;
        }
        String s = "C:\\Windows\\Users\\";
        Object[] ls = MiscTools.disectFilename(s).toArray();
        assertEquals("C:", ls[0]);
    }

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
        try {
            t = File.separator + "home" + File.separator + "daniel";
            u = MiscTools.makeFilenameRelative(s, t);
            fail();
        } catch (RuntimeException e) {
            assertTrue(true);
        }

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
        Assertions.assertFalse(containsWholeWord("foobar", "foo"));
        Assertions.assertFalse(containsWholeWord("bar", "foo"));
    }

    @Test
    public void testIsJMLComment() {
        assertTrue(isJMLComment("/*@iarijagjs"));
        assertTrue(isJMLComment("//@ sasahgue"));
        assertTrue(isJMLComment("//+KeY@"));
        assertTrue(isJMLComment("//-ESC@"));
        Assertions.assertFalse(isJMLComment("//-KeY@"));
        Assertions.assertFalse(isJMLComment("// @"));
        Assertions.assertFalse(isJMLComment("/*"));
        Assertions.assertFalse(isJMLComment("/**"));
    }

    /**
     * This is a test for the method {@link MiscTools#extractURI(DataLocation)}. It tests URI
     * extraction all four known kinds of DataLocations:
     * <ul>
     * <li>URLDataLocations</li>
     * <li>ArchiveDataLocations</li>
     * <li>SpecDataLocations</li>
     * <li>DataFileLocations</li>
     * </ul>
     * Note: This test creates two temporary files.
     */
    @Test
    public void testExtractURI() throws Exception {
        // test for URLDataLocation
        Path tmp = Files.createTempFile("test with whitespace", ".txt");
        URI tmpURI = tmp.toUri();
        DataLocation urlDataLoc = new URLDataLocation(tmpURI.toURL());
        assertEquals(tmpURI, MiscTools.extractURI(urlDataLoc).orElseThrow());

        // additional test for URLDataLocation with whitespace in filename
        Path tmpSpace = Files.createTempFile("test with whitespace", ".txt");
        URI tmpSpaceURI = tmpSpace.toUri();
        DataLocation urlDataLoc2 = new URLDataLocation(tmpSpaceURI.toURL());
        assertEquals(tmpSpaceURI, MiscTools.extractURI(urlDataLoc2).orElseThrow());

        // test for ArchiveDataLocation
        byte[] b = "test content".getBytes(StandardCharsets.UTF_8);
        Path zipP = Files.createTempFile("test with whitespace!", ".zip");

        try (FileOutputStream fos = new FileOutputStream(zipP.toFile());
                ZipOutputStream zos = new ZipOutputStream(fos)) {
            zos.putNextEntry(new ZipEntry("entry.txt"));
            zos.putNextEntry(new ZipEntry("entry with whitespace.txt"));
            zos.putNextEntry(new ZipEntry("entry with !bang!.txt"));
            zos.write(b);
        }

        try (ZipFile zf = new ZipFile(zipP.toFile())) {
            DataLocation entry0 = new ArchiveDataLocation(zf, "entry.txt");
            DataLocation entry1 = new ArchiveDataLocation(zf, "entry with whitespace.txt");
            DataLocation entry2 = new ArchiveDataLocation(zf, "entry with !bang!.txt");

            URI tmpZipURI = zipP.toUri();
            assertEquals("jar:" + tmpZipURI + "!/" + "entry.txt",
                MiscTools.extractURI(entry0).orElseThrow().toString());
            assertEquals("jar:" + tmpZipURI + "!/" + "entry%20with%20whitespace.txt",
                MiscTools.extractURI(entry1).orElseThrow().toString());
            URI read = MiscTools.extractURI(entry2).orElseThrow();

            // we can not simply use read.toURL().openStream(), because that uses caches and thus
            // keeps the file open (at least on Windows)
            URLConnection juc = read.toURL().openConnection();
            juc.setUseCaches(false);
            try (InputStream is = juc.getInputStream()) {
                Assertions.assertNotNull(is);
                // try if the file can be read correctly
                assertEquals(new String(b, StandardCharsets.UTF_8), IOUtil.readFrom(is));
            }
            assertEquals("jar:" + tmpZipURI + "!/" + "entry%20with%20!bang!.txt", read.toString());
        }

        // test for SpecDataLocation
        DataLocation specDataLoc = new SpecDataLocation("UNKNOWN", "unknown");
        assertEquals(Optional.empty(), MiscTools.extractURI(specDataLoc));

        // test for DataFileLocation
        DataLocation fileDataLoc = new DataFileLocation(tmp.toFile());
        assertEquals(tmpURI, MiscTools.extractURI(fileDataLoc).orElseThrow());

        // clean up temporary files
        Files.deleteIfExists(tmp);
        Files.deleteIfExists(tmpSpace);
        Files.deleteIfExists(zipP);
    }

    /**
     * This is a test for the method {@link MiscTools#parseURL(String)}. It tests for some strings
     * if they can be converted to URLs correctly. Note: This test creates a temporary zip file.
     *
     * @throws Exception if a string can not be converted successfully
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
        Assertions.assertNotNull(u1);

        // test file url string
        String correctURL = p.toUri().toURL().toString();
        URL u2 = MiscTools.parseURL(correctURL);
        Assertions.assertNotNull(u2);

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
        Assertions.assertNotNull(u3);

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
                Assertions.assertNotNull(is);
                // try if the file can be read correctly
                assertEquals(new String(b, StandardCharsets.UTF_8), IOUtil.readFrom(is));
            }

            // test reparsing jar url
            URL u4 = MiscTools.parseURL(entryURL.toString());
            Assertions.assertNotNull(u4);
            assertEquals(entryURL, u4);
        }

        // clean up temporary file
        Files.deleteIfExists(zipP);
    }
}
