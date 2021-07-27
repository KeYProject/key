/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.util.testcase.java;

import static org.junit.Assert.assertNotEquals;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.CharArrayWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URL;
import java.nio.charset.Charset;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.util.helper.HelperClassForUtilityTests;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.IOUtil.IFileVisitor;
import org.key_project.util.java.IOUtil.LineInformation;
import org.key_project.util.java.XMLUtil;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

/**
 * Tests for {@link IOUtil}
 * @author Martin Hentschel
 */
public class IOUtilTest extends TestCase {
   /**
    * Tests {@link IOUtil#getCurrentDirectory()}
    */
   @Test
   public void testGetCurrentDirectory() {
      File currentDir = IOUtil.getCurrentDirectory();
      assertNotNull(currentDir);
   }
   
   /**
    * Tests {@link IOUtil#exists(File)}
    */
   @Test
   public void testExists() throws IOException {
      assertFalse(IOUtil.exists(null));
      File tempFile = File.createTempFile("IOUtilTest_", ".testExists");
      assertTrue(IOUtil.exists(tempFile));
      tempFile.delete();
      assertFalse(IOUtil.exists(tempFile));
      File tempDir = IOUtil.createTempDirectory("IOUtilTest_", ".testExists");
      assertTrue(IOUtil.exists(tempDir));
      IOUtil.delete(tempDir);
      assertFalse(IOUtil.exists(tempDir));
   }
   
   /**
    * {@link IOUtil#contains(Iterable, File)}.
    */
   @Test
   public void testContains_Iterable() throws IOException {
      File yesDir = IOUtil.createTempDirectory("contains", "yes");
      File alsoYesDir = IOUtil.createTempDirectory("contains", "alsoYes");
      File noDir = IOUtil.createTempDirectory("contains", "no");
      try {
         File yesFile = HelperClassForUtilityTests.createFile(new File(yesDir, "Hello.txt"), "Hello");
         File yesFolder = HelperClassForUtilityTests.createFolder(new File(yesDir, "yesSub"));
         File yesSubFile = HelperClassForUtilityTests.createFile(new File(yesFolder, "Hello.txt"), "Hello");
         File alsoYesFile = HelperClassForUtilityTests.createFile(new File(alsoYesDir, "Hello.txt"), "Hello");
         File alsoYesFolder = HelperClassForUtilityTests.createFolder(new File(alsoYesDir, "yesSub"));
         File alsoYesSubFile = HelperClassForUtilityTests.createFile(new File(alsoYesFolder, "Hello.txt"), "Hello");
         File noFile = HelperClassForUtilityTests.createFile(new File(noDir, "Hello.txt"), "Hello");
         File noFolder = HelperClassForUtilityTests.createFolder(new File(noDir, "yesSub"));
         File noSubFile = HelperClassForUtilityTests.createFile(new File(noFolder, "Hello.txt"), "Hello");
         List<File> parents = CollectionUtil.toList(yesDir, alsoYesDir);
         assertFalse(IOUtil.contains((Iterable<File>)null, yesFile));
         assertFalse(IOUtil.contains(parents, null));
         assertFalse(IOUtil.contains((Iterable<File>)null, null));
         assertFalse(IOUtil.contains(parents, yesDir.getParentFile()));
         assertTrue(IOUtil.contains(parents, yesDir));
         assertTrue(IOUtil.contains(parents, yesFile));
         assertTrue(IOUtil.contains(parents, yesFolder));
         assertTrue(IOUtil.contains(parents, yesSubFile));
         assertTrue(IOUtil.contains(parents, alsoYesDir));
         assertTrue(IOUtil.contains(parents, alsoYesFile));
         assertTrue(IOUtil.contains(parents, alsoYesFolder));
         assertTrue(IOUtil.contains(parents, alsoYesSubFile));
         assertFalse(IOUtil.contains(parents, noDir));
         assertFalse(IOUtil.contains(parents, noFile));
         assertFalse(IOUtil.contains(parents, noFolder));
         assertFalse(IOUtil.contains(parents, noSubFile));
      }
      finally {
         IOUtil.delete(yesDir);
         IOUtil.delete(alsoYesDir);
         IOUtil.delete(noDir);
      }
   }
   
   /**
    * {@link IOUtil#contains(File, File)}.
    */
   @Test
   public void testContains_File() throws IOException {
      File yesDir = IOUtil.createTempDirectory("contains", "yes");
      File noDir = IOUtil.createTempDirectory("contains", "no");
      try {
         File yesFile = HelperClassForUtilityTests.createFile(new File(yesDir, "Hello.txt"), "Hello");
         File yesFolder = HelperClassForUtilityTests.createFolder(new File(yesDir, "yesSub"));
         File yesSubFile = HelperClassForUtilityTests.createFile(new File(yesFolder, "Hello.txt"), "Hello");
         File noFile = HelperClassForUtilityTests.createFile(new File(noDir, "Hello.txt"), "Hello");
         File noFolder = HelperClassForUtilityTests.createFolder(new File(noDir, "yesSub"));
         File noSubFile = HelperClassForUtilityTests.createFile(new File(noFolder, "Hello.txt"), "Hello");
         assertFalse(IOUtil.contains((File)null, yesFile));
         assertFalse(IOUtil.contains(yesDir, null));
         assertFalse(IOUtil.contains((File)null, null));
         assertFalse(IOUtil.contains(yesDir, yesDir.getParentFile()));
         assertTrue(IOUtil.contains(yesDir, yesDir));
         assertTrue(IOUtil.contains(yesDir, yesFile));
         assertTrue(IOUtil.contains(yesDir, yesFolder));
         assertTrue(IOUtil.contains(yesDir, yesSubFile));
         assertFalse(IOUtil.contains(yesDir, noDir));
         assertFalse(IOUtil.contains(yesDir, noFile));
         assertFalse(IOUtil.contains(yesDir, noFolder));
         assertFalse(IOUtil.contains(yesDir, noSubFile));
      }
      finally {
         IOUtil.delete(yesDir);
         IOUtil.delete(noDir);
      }
   }
   
   /**
    * {@link IOUtil#unifyLineBreaks(InputStream)}.
    */
   @Test
   public void testUnifyLineBreaks() throws IOException {
      doTestUnifyLineBreaks(null, null);
      doTestUnifyLineBreaks("A\nB\rC\n\nD\r\rE", "A\nB\nC\n\nD\n\nE");
      doTestUnifyLineBreaks("A\r\nE", "A\nE");
   }
   
   /**
    * Performs a test step of {@link #testUnifyLineBreaks()}.
    * @param toTest The {@link String} to test.
    * @param expected The expected result.
    * @throws IOException Occurred Exception.
    */
   protected void doTestUnifyLineBreaks(String toTest, String expected) throws IOException {
      ByteArrayInputStream in = toTest != null ? new ByteArrayInputStream(toTest.getBytes()) : null;
      InputStream converted = IOUtil.unifyLineBreaks(in);
      assertEquals(expected, IOUtil.readFrom(converted));
   }
   
   /**
    * Tests {@link IOUtil#computeMD5(File)}.
    */
   @Test
   public void testComputeMD5_File() throws IOException {
      // Test null
      try {
         IOUtil.computeMD5((File)null);
         fail("MD5 without File should not be possible.");
      }
      catch (IOException e) {
         assertEquals("Can't compute MD5 without a File.", e.getMessage());
      }
      // Test not existing file
      try {
         IOUtil.computeMD5(new File("NOT_EXISTING_FILE.txt"));
         fail("MD5 without existing File should not be possible.");
      }
      catch (IOException e) {
         assertEquals("Can't compute MD5, because \"NOT_EXISTING_FILE.txt\" is not an existing file.", e.getMessage());
      }
      // Test content
      File file = File.createTempFile("HelloWorld", ".txt");
      IOUtil.writeTo(new FileOutputStream(file), "Hello World");
      try {
         assertEquals("b10a8db164e0754105b7a99be72e3fe5", IOUtil.computeMD5(file));
      }
      finally {
         file.delete();
      }
   }

   /**
    * Tests {@link IOUtil#computeMD5(InputStream)}.
    */
   @Test
   public void testComputeMD5_InputStream() throws IOException {
      // Test null
      try {
         IOUtil.computeMD5((InputStream)null);
         fail("MD5 without InputStream should not be possible.");
      }
      catch (IOException e) {
         assertEquals("Can't compute MD5 without an InputStream.", e.getMessage());
      }
      // Test content
      TextInputStream in = new TextInputStream("Hello World");
      assertFalse(in.isClosed());
      assertEquals("b10a8db164e0754105b7a99be72e3fe5", IOUtil.computeMD5(in));
      assertTrue(in.isClosed());
   }

   /**
    * {@link InputStream} with a fixed text.
    * @author Martin Hentschel
    */
   private static class TextInputStream extends ByteArrayInputStream {
      /**
       * Is the stream closed?
       */
      private boolean closed = false;

      /**
       * Constructor.
       * @param text The fixed text.
       */
      public TextInputStream(String text) {
         super(text.getBytes());
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void close() throws IOException {
         this.closed = true;
         super.close();
      }

      /**
       * Checks if the stream is closed.
       * @return {@code true} closed, {@code false} open.
       */
      public boolean isClosed() {
         return closed;
      }
   }

   /**
    * Tests {@link IOUtil#visit(File, org.key_project.util.java.IOUtil.IFileVisitor)}.
    */
   @Test
   public void testVisit() throws IOException {
      // Create files to test
      File tempDir = IOUtil.createTempDirectory("ResourceUtilTest", "testCopyIntoWorkspace");
      try {
         File emptyFolder = new File(tempDir, "emptyFolder");
         emptyFolder.mkdirs();
         File subDir = new File(tempDir, "subFolder");
         subDir.mkdirs();
         File subFile = new File(subDir, "SubFile.txt");
         IOUtil.writeTo(new FileOutputStream(subFile), "SubFile.txt");
         File subSubDir = new File(subDir, "subSubFolder");
         subSubDir.mkdirs();
         File subSubA = new File(subSubDir, "SubSubFileA.txt");
         IOUtil.writeTo(new FileOutputStream(subSubA), "SubSubFileA.txt");
         File subSubB = new File(subSubDir, "SubSubFileB.txt");
         IOUtil.writeTo(new FileOutputStream(subSubB), "SubSubFileB.txt");
         File text = new File(tempDir, "Text.txt");
         IOUtil.writeTo(new FileOutputStream(text), "Text.txt");
         // Create visitor
         LogVisitor visitor = new LogVisitor();
         // Test null
         IOUtil.visit(null, visitor);
         assertEquals(0, visitor.getVisitedFiles().size());
         // Test visiting
         IOUtil.visit(tempDir, visitor);
         Collections.sort(visitor.getVisitedFiles(), new Comparator<File>() {
            @Override
            public int compare(File o1, File o2) {
                return o1.getAbsolutePath().compareTo(o2.getAbsolutePath());
            }
         }); // Ensure same order in all operating systems
         assertEquals(8, visitor.getVisitedFiles().size());
         assertEquals(tempDir, visitor.getVisitedFiles().get(0));
         assertEquals(text, visitor.getVisitedFiles().get(1));
         assertEquals(emptyFolder, visitor.getVisitedFiles().get(2));
         assertEquals(subDir, visitor.getVisitedFiles().get(3));
         assertEquals(subFile, visitor.getVisitedFiles().get(4));
         assertEquals(subSubDir, visitor.getVisitedFiles().get(5));
         assertEquals(subSubA, visitor.getVisitedFiles().get(6));
         assertEquals(subSubB, visitor.getVisitedFiles().get(7));
      }
      finally {
         IOUtil.delete(tempDir);
      }
   }
   
   /**
    * A logging {@link IFileVisitor}.
    * @author Martin Hentschel
    */
   private static final class LogVisitor implements IFileVisitor {
      /**
       * The visited {@link File}s.
       */
      private List<File> visitedFiles = new LinkedList<File>();

      /**
       * {@inheritDoc}
       */
      @Override
      public void visit(File file) throws IOException {
         visitedFiles.add(file);
      }

      /**
       * Returns the visited {@link File}s.
       * @return The visited {@link File}s.
       */
      public List<File> getVisitedFiles() {
         return visitedFiles;
      }
   }
   
   /**
    * Tests {@link IOUtil#search(File, org.key_project.util.java.IFilter)}.
    */
   @Test
   public void testSearch() throws IOException {
      // Create files to test
      File tempDir = IOUtil.createTempDirectory("ResourceUtilTest", "testCopyIntoWorkspace");
      try {
         File emptyFolder = new File(tempDir, "emptyFolder");
         emptyFolder.mkdirs();
         File subDir = new File(tempDir, "subFolder");
         subDir.mkdirs();
         File subFile = new File(subDir, "SubFile.txt");
         IOUtil.writeTo(new FileOutputStream(subFile), "SubFile.txt");
         File subSubDir = new File(subDir, "subSubFolder");
         subSubDir.mkdirs();
         File subSubA = new File(subSubDir, "SubSubFileA.txt");
         IOUtil.writeTo(new FileOutputStream(subSubA), "SubSubFileA.txt");
         File subSubB = new File(subSubDir, "SubSubFileB.txt");
         IOUtil.writeTo(new FileOutputStream(subSubB), "SubSubFileB.txt");
         File text = new File(tempDir, "Text.txt");
         IOUtil.writeTo(new FileOutputStream(text), "Text.txt");
         // Create filter
         IFilter<File> filter = new IFilter<File>() {
            @Override
            public boolean select(File element) {
               return element.getName().contains("Sub");
            }
         };
         // Test null
         List<File> result = IOUtil.search(null, filter);
         assertEquals(0, result.size());
         // Test no filter
         result = IOUtil.search(tempDir, null); 
         Collections.sort(result, new Comparator<File>() {
             @Override
             public int compare(File o1, File o2) {
                 return o1.getAbsolutePath().compareTo(o2.getAbsolutePath());
             }
          });  // Ensure same order in all operating systems
         assertEquals(8, result.size());
         assertEquals(tempDir, result.get(0));
         assertEquals(text, result.get(1));
         assertEquals(emptyFolder, result.get(2));
         assertEquals(subDir, result.get(3));
         assertEquals(subFile, result.get(4));
         assertEquals(subSubDir, result.get(5));
         assertEquals(subSubA, result.get(6));
         assertEquals(subSubB, result.get(7));
         // Test with filter
         result = IOUtil.search(tempDir, filter);
         Collections.sort(result,new Comparator<File>() {
             @Override
             public int compare(File o1, File o2) {
                 return o1.getAbsolutePath().compareTo(o2.getAbsolutePath());
             }
          }); // Ensure same order in all operating systems
         assertEquals(4, result.size());
         assertEquals(subFile, result.get(0));
         assertEquals(subSubDir, result.get(1));
         assertEquals(subSubA, result.get(2));
         assertEquals(subSubB, result.get(3));
      }
      finally {
         IOUtil.delete(tempDir);
      }
   }
   
   /**
    * Tests {@link IOUtil#getFileExtension(File)}
    */
   @Test
   public void testGetFileExtension() {
      assertNull(IOUtil.getFileExtension(null));
      assertNull(IOUtil.getFileExtension(new File("")));
      assertNull(IOUtil.getFileExtension(new File("hello")));
      assertNull(IOUtil.getFileExtension(new File("path", "hello")));
      assertEquals("java", IOUtil.getFileExtension(new File("hello.java")));
      assertEquals("java", IOUtil.getFileExtension(new File("path", "hello.java")));
      assertEquals("java", IOUtil.getFileExtension(new File(".java")));
      assertEquals("java", IOUtil.getFileExtension(new File("path", ".java")));
      assertEquals("", IOUtil.getFileExtension(new File(".")));
      assertEquals("", IOUtil.getFileExtension(new File("path", ".")));
      assertEquals("", IOUtil.getFileExtension(new File("hello.")));
      assertEquals("", IOUtil.getFileExtension(new File("path", "hello.")));
   }
   
   /**
    * Tests {@link IOUtil#getHomeDirectory()}.
    */
   @Test
   public void testGetHomeDirectory() {
      File home = IOUtil.getHomeDirectory();
      assertNotNull(home);
      assertEquals(System.getProperty("user.home"), home.toString());
   }
   
   /**
    * Tests {@link IOUtil#getFileNameWithoutExtension(String)}.
    */
   @Test
   public void testGetFileNameWithoutExtension() {
      assertNull(IOUtil.getFileNameWithoutExtension(null));
      assertEquals("test", IOUtil.getFileNameWithoutExtension("test.txt"));
      assertEquals("hello.world", IOUtil.getFileNameWithoutExtension("hello.world.diagram"));
      assertEquals("", IOUtil.getFileNameWithoutExtension(".project"));
      assertEquals("", IOUtil.getFileNameWithoutExtension(""));
      assertEquals("file", IOUtil.getFileNameWithoutExtension("file"));
   }

   /**
    * Tests {@link IOUtil#createTempDirectory(String, String)}.
    */
   @Test
   public void testCreateTempDirectory() throws IOException {
      File tempDir = null;
      try {
         tempDir = IOUtil.createTempDirectory("IOUtilTest", "testCreateTempDirectory");
         assertNotNull(tempDir);
         assertTrue(tempDir.exists());
         assertTrue(tempDir.isDirectory());
         assertTrue(tempDir.getName().startsWith("IOUtilTest"));
         assertTrue(tempDir.getName().endsWith("testCreateTempDirectory"));
      }
      finally {
         IOUtil.delete(tempDir);
      }
   }
   
   /**
    * Tests {@link LineInformation#normalizeColumn(int, int)}.
    */
   @Test
   public void testLineInformationNormalizeColumn() throws IOException {
      // Test different tab width
      doTestLineInformationNormalizeColumn("AB\tCD EF GH\t\tIJ\t.", 
                                           3, 
                                           new int[] {0, 1, 2, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 11, 11, 12, 12, 12, 13, 14, 15, 15, 15, 16, 17, 18});
      doTestLineInformationNormalizeColumn("AB\tCD EF GH\t\tIJ\t.", 
                                           2, 
                                           new int[] {0, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 11, 12, 12, 13, 14, 15, 15, 16, 17, 18});
      doTestLineInformationNormalizeColumn("AB\tCD EF GH\t\tIJ\t.", 
                                           1, 
                                           new int[] {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18});
      doTestLineInformationNormalizeColumn("AB\tCD EF GH\t\tIJ\t.", 
                                           0, // Invalid, column index is expected as result.
                                           new int[] {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18});
      doTestLineInformationNormalizeColumn("AB\tCD EF GH\t\tIJ\t.", 
                                           -1, // Invalid, column index is expected as result.
                                           new int[] {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18});
      // Test invalid column index
      LineInformation[] infos = IOUtil.computeLineInformation(new ByteArrayInputStream("AB\tCD EF GH\t\tIJ\t.".getBytes()));
      assertNotNull(infos);
      assertEquals(1, infos.length);
      LineInformation info = infos[0];
      assertNotNull(info);
      assertEquals(-1, info.normalizeColumn(-1, 3));
      assertEquals(-2, info.normalizeColumn(-2, 3));
      // Test tabs only
      doTestLineInformationNormalizeColumn("\t\t\t\t\t", 
                                           3, 
                                           new int[] {0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 7});
   }
   
   /**
    * Executes a test for {@link #testLineInformationNormalizeColumn()}.
    * @param text The text to use.
    * @param tabWidth The tab width to use.
    * @param expectedIndices The expected normalized indices.
    * @throws IOException Occurred Exception.
    */
   protected void doTestLineInformationNormalizeColumn(String text, int tabWidth, int[] expectedIndices) throws IOException {
      // Compute line information
      LineInformation[] infos = IOUtil.computeLineInformation(new ByteArrayInputStream(text.getBytes()));
      assertNotNull(infos);
      assertEquals(1, infos.length);
      LineInformation info = infos[0];
      assertNotNull(info);
      // Test column normalization
      for (int i = 0; i < expectedIndices.length; i++) {
         int normalColumn = info.normalizeColumn(i, tabWidth);
         //System.out.println("normalizeColumn(" + i + ", " + tabWidth + ") = " + normalColumn + (normalColumn < text.toCharArray().length ? (" which is character '" + text.toCharArray()[normalColumn] + "'") : ""));
         assertEquals(expectedIndices[i], normalColumn); 
      }
   }
   
   /**
    * Tests {@link IOUtil#computeLineInformation(File)}
    */
   @Test
   public void testComputeLineInformation_File() throws IOException {
      // Get test file
      File textFile = new File(HelperClassForUtilityTests.RESOURCE_DIRECTORY + File.separator + "lineIndicesTest" + File.separator + "Text.txt");
      assertTrue("File '" + textFile + "' does not exist.", textFile.isFile());
      // Test null
      assertLineInformation((File)null);
      // Test unix file
      assertLineInformation(convertTextFile(textFile, "Text_Unix.txt", "\r"), 0, 1, 2, 9, 16, 17, 24, 50, 23661, 23662, 23663, 23671, 23672);
      // Test mac file
      assertLineInformation(convertTextFile(textFile, "Text_Mac.txt", "\n"), 0, 1, 2, 9, 16, 17, 24, 50, 23661, 23662, 23663, 23671, 23672);
      // Test dos file
      assertLineInformation(convertTextFile(textFile, "Text_DOS.txt", "\r\n"), 0, 2, 4, 12, 20, 22, 30, 57, 23669, 23671, 23673, 23682, 23684);
   }
   
   /**
    * <p>
    * Creates a new text file with the given name which contains the
    * content of the given source {@link File} but with the new defined
    * line breaks.
    * </p>
    * <p>
    * This method is required because GIT changes the line breaks. For this
    * reason it is not possible to commit/checkout the test data files directly.
    * </p>
    * @param source The {@link File} with the source text.
    * @param newFileName The new file name.
    * @param lineBreak The line break to use.
    * @return The created {@link File} with the same text but with new line breaks.
    * @throws IOException Occurred Exception
    */
   protected File convertTextFile(File source, String newFileName, String lineBreak) throws IOException {
      assertNotNull(source);
      assertTrue(source.exists());
      assertNotNull(newFileName);
      // Create new file content
      CharArrayWriter writer = new CharArrayWriter();
      BufferedReader reader = new BufferedReader(new InputStreamReader(new FileInputStream(source)));
      try {
         String line = null;
         while ((line = reader.readLine()) != null) {
            writer.write(line);
            writer.write(lineBreak);
         }
         String newText = writer.toString();
         // Create new file
         File target = new File(source.getParentFile(), newFileName);
         try (FileWriter targetWriter = new FileWriter(target)) {
            targetWriter.write(newText);
         }
         return target;
      }
      finally {
         reader.close();
         writer.close();
      }
   }

   /**
    * Makes sure that for the given text the correct line start indices are computed.
    * @param text The text to test.
    * @param expectedIndices The expected line indices.
    * @throws IOException Occurred Exception.
    */
   protected void assertLineInformation(File file, int... expectedIndices) throws IOException {
      LineInformation[] result = IOUtil.computeLineInformation(file != null ? file : null);
      assertNotNull(result);
      assertEquals(expectedIndices.length, result.length);
      for (int i = 0; i < expectedIndices.length; i++) {
         assertNotNull(result[i]);
         assertEquals(expectedIndices[i], result[i].getOffset());
      }
   }
   
   /**
    * Tests {@link IOUtil#computeLineInformation(java.io.InputStream)}
    */
   @Test
   public void testComputeLineInformation_InputStream() throws IOException {
      doTestComputeLineInformation_InputStream("\n");
      doTestComputeLineInformation_InputStream("\r");
      doTestComputeLineInformation_InputStream("\r\n");
   }

   /**
    * Executes the tests for {@link #testComputeLineInformation_InputStream()}
    * with the given line break sign.
    * @param newLine The line break sign to use.
    * @throws IOException Occurred Exception.
    */
   protected void doTestComputeLineInformation_InputStream(String newLine) throws IOException {
      // Test null
      assertLineInformation(newLine, new String[0]);
      // Test single line
      assertLineInformation(newLine, "Hello World!");
      // Test two line
      assertLineInformation(newLine, "Hello World!", "Hello World Again!");
      // Test three lines with one empty line
      assertLineInformation(newLine, "Hello World!", "Hello World Again!", "", "Fourth Line");
      // Test double empty line
      assertLineInformation(newLine, "1", "", "", "4");
      // Test file with only line breaks
      assertLineInformation(newLine, "", "", "", "", "", "", "", "","", "", "", "");
      // Test one previous empty line
      assertLineInformation(newLine, "", "Hello World!");
      // Test two previous empty line
      assertLineInformation(newLine, "", "", "Hello World!");
      // Test one following empty line
      assertLineInformation(newLine, "Hello World!", "");
      // Test two following empty line
      assertLineInformation(newLine, "Hello World!", "", "");
      // Test one previous and following empty line
      assertLineInformation(newLine, "", "Hello World!", "");
      // Test two previous and following empty line
      assertLineInformation(newLine, "", "", "Hello World!", "", "");
      // Test two previous and following empty line
      assertLineInformation(newLine, "", "", "Hello World!", "", "");
      // Test example documentation
      assertLineInformation(newLine, "Line 1", "Line 2:\tWith some text", "", "Line 4");
      // Test tabs
      assertLineInformation(newLine, "", "\t", "\t\t", "", "\t\t\t\t");
      assertLineInformation(newLine, "", "\tAA", "\tBB\tCC", "", "\t\tDD\tEE\t");
   }
   
   /**
    * Constructs a text for the given lines and tests the computed
    * start line indices.
    * @param newLine The new line sign to use.
    * @param textLines The lines of text.
    * @throws IOException Occurred Exception.
    */
   protected void assertLineInformation(String newLine, String... textLines) throws IOException {
      if (textLines != null) {
         StringBuffer sb = new StringBuffer();
         LineInformation[] expectedInfos = new LineInformation[textLines.length];
         int lastIndex = 0;
         for (int i = 0; i < textLines.length; i++) {
            // Compute tabs
            List<Integer> tabIndices = new LinkedList<Integer>();
            char[] lineChars = textLines[i].toCharArray();
            for (int j = 0; j < lineChars.length; j++) {
               if ('\t' == lineChars[j]) {
                  tabIndices.add(Integer.valueOf(j));
               }
            }
            // Compute line
            expectedInfos[i] = new LineInformation(lastIndex, tabIndices);
            sb.append(textLines[i]);
            lastIndex += textLines[i].length();
            if (i < textLines.length - 1) {
               sb.append(newLine);
               lastIndex += newLine.length();
            }
         }
         assertLineInformation(sb.length() >= 1 ? sb.toString() : null, expectedInfos);
      }
      else {
         assertLineInformation((String)null, new LineInformation[0]);
      }
   }

   /**
    * Makes sure that for the given text the correct line start indices are computed.
    * @param text The text to test.
    * @param expectedInfos The expected line informations.
    * @throws IOException Occurred Exception.
    */
   protected void assertLineInformation(String text, LineInformation... expectedInfos) throws IOException {
      LineInformation[] result = IOUtil.computeLineInformation(text != null ? new ByteArrayInputStream(text.getBytes()) : null);
      assertNotNull(text, result);
      assertEquals(text, expectedInfos.length, result.length);
      for (int i = 0; i < expectedInfos.length; i++) {
         assertNotNull(expectedInfos[i]);
         assertNotNull(result[i]);
         assertEquals(text + " at " + i, expectedInfos[i].getOffset(), result[i].getOffset());
         assertNotNull(expectedInfos[i].getTabIndices());
         assertNotNull(result[i].getTabIndices());
         assertEquals(expectedInfos[i].getTabIndices().length, result[i].getTabIndices().length);
         for (int j = 0; j < expectedInfos[i].getTabIndices().length; j++) {
            assertEquals(expectedInfos[i].getTabIndices()[j], result[i].getTabIndices()[j]);
         }
      }
   }
   
   /**
    * Tests {@link IOUtil#writeTo(java.io.OutputStream, String)}
    */
   @Test
   public void testWriteTo() throws IOException {
      File tempFile = null;
      try {
         // Test null stream, nothing should happen
         String content = "Hello World!";
         IOUtil.writeTo(null, content);
         // Test null content
         ByteArrayOutputStream out = new ByteArrayOutputStream();
         IOUtil.writeTo(out, null);
         assertEquals(0, out.toByteArray().length);
         // Test writing to memory stream
         out = new ByteArrayOutputStream();
         IOUtil.writeTo(out, content);
         assertEquals(content, out.toString());
         // Test writing to temporary file
         tempFile = File.createTempFile("IOUtilTest", "testWriteTo.txt");
         IOUtil.writeTo(new FileOutputStream(tempFile), content);
         assertEquals(content, IOUtil.readFrom(new FileInputStream(tempFile)));
      }
      finally {
         if (tempFile != null) {
             tempFile.delete();
         }
      }
   }
   
   /**
    * Tests {@link IOUtil#writeTo(java.io.OutputStream, String, java.nio.charset.Charset)}
    */
   @Test
   public void testWriteTo_Charstet() throws Exception {
      byte[] utf8 = doWriteCharsetAsXmlTest("Hello \u201Cworld\u201D\u2026", Charset.forName("UTF-8"));
      byte[] utf16 = doWriteCharsetAsXmlTest("Hello \u201Cworld\u201D\u2026", Charset.forName("UTF-16"));
      assertNotEquals(utf8.length, utf16.length);
   }
   
   /**
    * Performs test steps of {@link #testWriteTo_Charstet()}.
    * @param text The text to write.
    * @param encoding The encoding to use.
    * @return The written bytes.
    * @throws Exception Occurred Exception.
    */
   protected byte[] doWriteCharsetAsXmlTest(String text, Charset encoding) throws Exception {
      // Create XML
      StringBuffer sb = new StringBuffer();
      XMLUtil.appendXmlHeader(encoding != null ? encoding.displayName() : null, sb);
      Map<String, String> attributes = new LinkedHashMap<String, String>();
      attributes.put("text", XMLUtil.encodeText(text));
      XMLUtil.appendEmptyTag(0, "root", attributes, sb);
      // Write content
      ByteArrayOutputStream out = new ByteArrayOutputStream();
      IOUtil.writeTo(out, sb.toString(), encoding);
      // Parse output stream
      SAXParserFactory factory = SAXParserFactory.newInstance();
      factory.setNamespaceAware(true);
      SAXParser saxParser = factory.newSAXParser();
      RootHandler handler = new RootHandler();
      saxParser.parse(new ByteArrayInputStream(out.toByteArray()), handler);
      // Ensure that loaded text is the same
      assertEquals(text, handler.getText());
      return out.toByteArray();
   }
   
   /**
    * Helper class of {@link IOUtilTest#doWriteCharsetAsXmlTest(String, Charset)}.
    * @author Martin Hentschel
    */
   private static final class RootHandler extends DefaultHandler {
      /**
       * The parsed text.
       */
      private String text;

      /**
       * {@inheritDoc}
       */
      @Override
      public void startElement(String uri, String localName, String qName, Attributes attributes) throws SAXException {
         if ("root".equals(qName)) {
            if (text == null) {
               text = attributes.getValue("text");
            }
            else {
               throw new SAXException("Found root multiple times.");
            }
         }
         else {
            throw new SAXException("Unspported element: " + qName);
         }
      }

      /**
       * Returns the parsed text.
       * @return The parsed text.
       */
      public String getText() {
         return text;
      }
   }
   
   /**
    * Tests {@link IOUtil#readFrom(File)}
    */
   @Test
   public void testReadFrom_File() throws IOException {
      // Test null
      assertNull(IOUtil.readFrom((File)null));
      File tempFile = File.createTempFile("IOUtilTest", "testReadFrom_File");
      try {
         // Test not existing file
         IOUtil.delete(tempFile);
         assertFalse(tempFile.exists());
         assertNull(IOUtil.readFrom(tempFile));
         // Test existing file
         IOUtil.writeTo(new FileOutputStream(tempFile), "Hello World!");
         assertEquals("Hello World!", IOUtil.readFrom(tempFile));
      }
      finally {
         IOUtil.delete(tempFile);
      }
   }
   
   /**
    * Tests {@link IOUtil#readFrom(java.io.InputStream)}
    */
   @Test
   public void testReadFrom_InputStream() {
      try {
         doTestReadFrom(null);
         doTestReadFrom("One Line");
         doTestReadFrom("First Line\n\rSecond Line");
         doTestReadFrom("One Line\r");
         doTestReadFrom("One Line\n");
         doTestReadFrom("One Line\r\n");
         doTestReadFrom("One Line\n\r");
         StringBuffer sb = new StringBuffer();
         for (int i = 0; i < IOUtil.BUFFER_SIZE * 3; i++) {
            sb.append("A");
         }
         doTestReadFrom(sb.toString());
      }
      catch (IOException e) {
         e.printStackTrace();
         fail();
      }
   }
   
   /**
    * Executes the assertions for {@link #testReadFrom()}.
    * @param text The text to check.
    * @throws IOException Occurred Exception.
    */
   protected void doTestReadFrom(String text) throws IOException {
      if (text != null) {
         assertEquals(text, IOUtil.readFrom(new ByteArrayInputStream(text.getBytes())));
      }
      else {
         assertNull(IOUtil.readFrom((InputStream)null));
      }
   }
   
   /**
    * Tests {@link IOUtil#delete(File)}.
    */
   @Test
   public void testDelete() throws IOException {
       // Test null
       IOUtil.delete(null); // No exception expected
       // Test existing file
       File tmpFile = File.createTempFile("IOUtilTest", "deleteMe");
       assertTrue(tmpFile.exists());
       IOUtil.delete(tmpFile);
       assertFalse(tmpFile.exists());
       // Test empty directory
       HelperClassForUtilityTests.createFolder(tmpFile);
       IOUtil.delete(tmpFile);
       assertFalse(tmpFile.exists());
       // Test directory with content
       HelperClassForUtilityTests.createFolder(tmpFile);
       File subDir = HelperClassForUtilityTests.createFolder(new File(tmpFile, "subDir"));
       File subFile = HelperClassForUtilityTests.createFile(new File(tmpFile, "subFile.txt"), "test");
       File subDir2 = HelperClassForUtilityTests.createFolder(new File(tmpFile, "subDir"));
       File subSubDir2 = HelperClassForUtilityTests.createFolder(new File(subDir2, "subDir"));
       File subSubSubDir2 = HelperClassForUtilityTests.createFolder(new File(subSubDir2, "subDir"));
       File subSubSubDir2File = HelperClassForUtilityTests.createFile(new File(subSubSubDir2, "subFile.txt"), "test");
       IOUtil.delete(tmpFile);
       assertFalse(tmpFile.exists());
       assertFalse(subDir.exists());
       assertFalse(subFile.exists());
       assertFalse(subDir2.exists());
       assertFalse(subSubDir2.exists());
       assertFalse(subSubSubDir2.exists());
       assertFalse(subSubSubDir2File.exists());
   }
   
   /**
    * Tests {@link IOUtil#copy(InputStream, java.io.OutputStream)}.
    */
   @Test
   public void testCopy() throws IOException {
      doTestCopy(null);
      assertFalse(IOUtil.copy(null, null));
      assertFalse(IOUtil.copy(new ByteArrayInputStream("NotCopied".getBytes()), null));
      doTestCopy("One Line");
      doTestCopy("First Line\n\rSecond Line");
      doTestCopy("One Line\r");
      doTestCopy("One Line\n");
      doTestCopy("One Line\r\n");
      doTestCopy("One Line\n\r");
      StringBuffer sb = new StringBuffer();
      for (int i = 0; i < IOUtil.BUFFER_SIZE * 3; i++) {
         sb.append("A");
      }
      doTestCopy(sb.toString());
   }
   
   /**
    * Executes the assertions for {@link #testCopy()}.
    * @param text The text to check.
    * @throws IOException Occurred Exception.
    */
   protected void doTestCopy(String text) throws IOException {
      if (text != null) {
         byte[] inBytes = text.getBytes();
         ByteArrayInputStream in = new ByteArrayInputStream(inBytes);
         ByteArrayOutputStream out = new ByteArrayOutputStream();
         assertTrue(IOUtil.copy(in, out));
         byte[] outBytes = out.toByteArray();
         assertEquals(inBytes.length, outBytes.length);
         for (int i = 0; i < inBytes.length; i++) {
            assertEquals(inBytes[i], outBytes[i]);
         }
      }
      else {
         assertFalse(IOUtil.copy(null, new ByteArrayOutputStream()));
      }
   }
   
   /**
    * Tests {@link IOUtils#getClassLocation(Class)}
    */
   @Test
   public void testGetClassLocation() {
      assertNull(IOUtil.getClassLocation(null));
      assertNotNull(IOUtil.getClassLocation(getClass()));
   }
   
   /**
    * Tests {@link IOUtils#getProjectRoot(Class)}
    */
   @Test
   public void testGetProjectRoot() {
      assertNull(IOUtil.getProjectRoot(null));
      assertNotNull(IOUtil.getProjectRoot(getClass()));
   }
   
   /**
    * Tests {@link IOUtils#toURI(java.net.URL)}
    * @throws MalformedURLException Occurred Exception
    */
   @Test
   public void testToURI() throws Exception {
      // Test null
      assertNull(IOUtil.toURI(null));
      // Test web URL
      URL url = new URL("https://www.google.de");
      URI uri = IOUtil.toURI(url);
      assertNotNull(uri);
      assertEquals(url.toString(), uri.toString());
      // Test web URL mit query
      url = new URL("https://www.google.de/webhp?sourceid=chrome-instant&ion=1&espv=2&ie=UTF-8#q=test");
      uri = IOUtil.toURI(url);
      assertNotNull(uri);
      assertEquals(url.toString(), uri.toString());
      // Test file URL
      url = new URL("file:/D:/Forschung/Tools/eclipse 4.4 SR1 (64bit)/../../GIT/R/KeY4Eclipse/src/plugins/org.key_project.ui/");
      uri = IOUtil.toURI(url);
      assertNotNull(uri);
      assertEquals("file:/D:/Forschung/Tools/eclipse%204.4%20SR1%20(64bit)/../../GIT/R/KeY4Eclipse/src/plugins/org.key_project.ui/", uri.toString());
   }
   
   /**
    * Tests {@link IOUtils#toFile(URL)}
    * @throws MalformedURLException Occurred Exception
    */
   @Test
   public void testToFile() throws MalformedURLException {
      // Test null
      assertNull(IOUtil.toFile(null));
      // Test file uri
      assertEquals(new File("/tmp/Test/Test.xml"), IOUtil.toFile(new URL("file:///tmp/Test/Test.xml")));
      // Test web
      try {
         IOUtil.toFile(new URL("http://www.google.de"));
         fail("Exception expected");
      }
      catch (IllegalArgumentException e) {
      }
   }
   
   /**
    * Tests {@link IOUtils#toFileString(URL)}
    * @throws MalformedURLException Occurred Exception
    */
   @Test
   public void testToFileString() throws MalformedURLException {
      // Test null
      assertNull(IOUtil.toFileString(null));
      // Test file uri
      assertEquals(File.separator + "tmp" + File.separator + "Test" + File.separator + "Test.xml", IOUtil.toFileString(new URL("file:///tmp/Test/Test.xml")));
      // Test web
      try {
         IOUtil.toFileString(new URL("http://www.google.de"));
         fail("Exception expected");
      }
      catch (IllegalArgumentException e) {
      }
   }
   
   /**
    * Tests {@link IOUtil#validateOSIndependentFileName(String)}
    */
   @Test
   public void testValidateOSIndependentFileName() {
      assertEquals(null, IOUtil.validateOSIndependentFileName(null));
      assertEquals("Hello_World", IOUtil.validateOSIndependentFileName("Hello World"));
      assertEquals("Hello_World_txt", IOUtil.validateOSIndependentFileName("Hello World.txt"));
      assertEquals("Hello__World_txt", IOUtil.validateOSIndependentFileName("Hello<>World.txt"));
      assertEquals("Hello__World_txt", IOUtil.validateOSIndependentFileName("Hello::World.txt"));
      assertEquals("_Hello_World___txt_", IOUtil.validateOSIndependentFileName(".Hello.World...txt."));
   }
}