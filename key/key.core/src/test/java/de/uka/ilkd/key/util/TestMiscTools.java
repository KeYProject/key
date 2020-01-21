// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util;


import static de.uka.ilkd.key.util.MiscTools.containsWholeWord;
import static de.uka.ilkd.key.util.MiscTools.isJMLComment;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;
import java.util.zip.ZipOutputStream;

import de.uka.ilkd.key.java.recoderext.URLDataLocation;
import junit.framework.TestCase;
import recoder.io.ArchiveDataLocation;
import recoder.io.DataFileLocation;
import recoder.io.DataLocation;

public class TestMiscTools extends TestCase {

    public void testDisectFilenameUnix() {
        // run only on UNIX-like systems
        if (File.separatorChar != '/') return;
        String s = "/home/daniel//workspace/key";
        Object[] ls = MiscTools.disectFilename(s).toArray();
        assertEquals("",ls[0]);
        assertEquals("key",ls[4]);
        s = s.substring(1);
        ls = MiscTools.disectFilename(s).toArray();
        assertEquals("home",ls[0]);
        s = s+"/";
        ls = MiscTools.disectFilename(s).toArray();
        assertEquals(4,ls.length);
        assertEquals("key",ls[3]);
        s = "."+s;
        ls = MiscTools.disectFilename(s).toArray();
        assertEquals(4,ls.length);
        assertEquals("key",ls[3]);
    }
    
    public void testDisectFilenameWindows() {
        // run only on Windows systems
        if (File.separatorChar != '\\') return;
        String s = "C:\\Windows\\Users\\";
        Object[] ls = MiscTools.disectFilename(s).toArray();
        assertEquals("C:",ls[0]);
    }
    
    public void testMakeFilenameRelativeUnix() {
        // run only on UNIX-like systems
        if (File.separatorChar != '/') return;
        
        String s = "/home/daniel/bla";
        String t = "/home/daniel/blubb";
        String u = MiscTools.makeFilenameRelative(s,t);
        assertEquals("../bla",u);
        // s shorter than t
        t = "/home/daniel/bla/foo/bar";
        u = MiscTools.makeFilenameRelative(s, t);
        assertEquals("../..",u);
        // s already relative
        s = s.substring(1);
        assertEquals(s,MiscTools.makeFilenameRelative(s, t));
        s = "/home/../home/daniel/";
        t = "/home";
        assertEquals("daniel", MiscTools.makeFilenameRelative(s, t));
    }
    
    public void testMakeFilenameRelativeWindows() {
        // run only on Windows systems
        if (File.separatorChar != '\\') return;
        
        // test windows delimiters
        String s = "C:\\Windows";
        String t = "c:\\";
        String u = MiscTools.makeFilenameRelative(s, t);
        assertEquals("Windows",u);
        // do stupid things
        try {
            t = File.separator + "home" + File.separator + "daniel";
            u = MiscTools.makeFilenameRelative(s, t);
            fail();
        } catch (RuntimeException e){
            assertTrue(true);
        }
        
    }
    
    public void testToValidFileName(){
        assertEquals("foo_bar", MiscTools.toValidFileName("foo:bar"));
        assertEquals("foo_bar", MiscTools.toValidFileName("foo\\bar"));
        assertEquals("foo(bar)", MiscTools.toValidFileName("foo[bar]"));
    }
    
    public void testContainsWholeWord(){
        assertTrue(containsWholeWord("foo bar","foo"));
        assertTrue(containsWholeWord("foo;","foo"));
        assertTrue(containsWholeWord("\rfoo\t","foo"));
        assertTrue(containsWholeWord(" foo foo","foo"));
        assertFalse(containsWholeWord("foobar","foo"));
        assertFalse(containsWholeWord("bar","foo"));
    }
    
    public void testIsJMLComment(){
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
     * This is a test for the method {@link MiscTools#extractURI(DataLocation)}.
     * It tests URI extraction all four known kinds of DataLocations:<ul>
     *     <li>URLDataLocations</li>
     *     <li>ArchiveDataLocations</li>
     *     <li>SpecDataLocations</li>
     *     <li>DataFileLocations</li>
     * </ul>
     * Note: This test creates two temporary files.
     */
    public void testExtractURI() {
        try {
            Path tmp = Files.createTempFile("test", ".txt");
            URI tmpURI = tmp.toUri();
            DataLocation urlDataLoc = new URLDataLocation(tmpURI.toURL());
            assertEquals(tmpURI, MiscTools.extractURI(urlDataLoc));

            Path zipP = Files.createTempFile("test", ".zip");
            FileOutputStream fos = new FileOutputStream(zipP.toFile());
            ZipOutputStream zos = new ZipOutputStream(fos);
            zos.putNextEntry(new ZipEntry("entry0.txt"));
            zos.write("test content".getBytes());
            zos.close();
            fos.close();

            ZipFile zf = new ZipFile(zipP.toFile());
            DataLocation archiveDataLoc = new ArchiveDataLocation(zf, "entry0.txt");
            zf.close();
            URI tmpZipURI = zipP.toUri();
            assertEquals("jar:" + tmpZipURI + "!/" + "entry0.txt",
                    MiscTools.extractURI(archiveDataLoc).toString());

            DataLocation specDataLoc = new SpecDataLocation("UNKNOWN", "unknown");
            assertEquals("UNKNOWN://unknown", MiscTools.extractURI(specDataLoc).toString());

            DataLocation fileDataLoc = new DataFileLocation(tmp.toFile());
            assertEquals(tmpURI, MiscTools.extractURI(fileDataLoc));

            // clean up temporary files
            Files.deleteIfExists(tmp);
            Files.deleteIfExists(zipP);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}