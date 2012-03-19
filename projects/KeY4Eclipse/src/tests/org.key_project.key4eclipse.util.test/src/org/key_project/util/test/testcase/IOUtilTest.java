package org.key_project.util.test.testcase;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.junit.Test;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.test.Activator;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for {@link IOUtil}
 * @author Martin Hentschel
 */
public class IOUtilTest extends TestCase {
   @Test
   public void testDebug() throws IOException {
//      assertLineIndices("\r\n", "Hello World!", "Hello World Again!");
      assertLineIndices("\r", "Hello World!", "Hello World Again!", "", "Fourth Line");
   }
   
   /**
    * Tests {@link IOUtil#computeLineStartIndices(File)}
    */
   @Test
   public void testComputeLineStartIndices_File() throws IOException, CoreException {
      // Create test files
      IProject project = TestUtilsUtil.createProject("IOUtilTest_testComputeLineStartIndices_File"); 
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/lineIndicesTest", project);
      // Test null
      assertLineIndices((IFile)null);
      // Test unix file
      assertLineIndices(project.getFile("Text_Unix.txt"), 0, 1, 2, 9, 16, 17, 24, 50, 23661, 23662, 23663, 23671, 23672);
      // Test mac file
      assertLineIndices(project.getFile("Text_Mac.txt"), 0, 1, 2, 9, 16, 17, 24, 50, 23661, 23662, 23663, 23671, 23672);
      // Test dos file
      assertLineIndices(project.getFile("Text_DOS.txt"), 0, 2, 4, 12, 20, 22, 30, 57, 23669, 23671, 23673, 23682, 23684);
   }

   /**
    * Makes sure that for the given text the correct line start indices are computed.
    * @param text The text to test.
    * @param expectedIndices The expected line indices.
    * @throws IOException Occurred Exception.
    */
   protected void assertLineIndices(IFile file, int... expectedIndices) throws IOException {
      Integer[] result = IOUtil.computeLineStartIndices(file != null ? ResourceUtil.getLocation(file) : null);
      assertNotNull(result);
      assertEquals(expectedIndices.length, result.length);
      for (int i = 0; i < expectedIndices.length; i++) {
         assertEquals(expectedIndices[i], result[i].intValue());
      }
   }
   
   /**
    * Tests {@link IOUtil#computeLineStartIndices(java.io.InputStream)}
    */
   @Test
   public void testComputeLineStartIndices_InputStream() throws IOException {
      doTestComputeLineStartIndices_InputStream("\n");
      doTestComputeLineStartIndices_InputStream("\r");
      doTestComputeLineStartIndices_InputStream("\r\n");
   }

   /**
    * Executes the tests for {@link #testComputeLineStartIndices_InputStream()}
    * with the given line break sign.
    * @param newLine The line break sign to use.
    * @throws IOException Occurred Exception.
    */
   protected void doTestComputeLineStartIndices_InputStream(String newLine) throws IOException {
      // Test null
      assertLineIndices(newLine, new String[0]);
      // Test single line
      assertLineIndices(newLine, "Hello World!");
      // Test two line
      assertLineIndices(newLine, "Hello World!", "Hello World Again!");
      // Test three lines with one empty line
      assertLineIndices(newLine, "Hello World!", "Hello World Again!", "", "Fourth Line");
      // Test double empty line
      assertLineIndices(newLine, "1", "", "", "4");
      // Test file with only line breaks
      assertLineIndices(newLine, "", "", "", "", "", "", "", "","", "", "", "");
      // Test one previous empty line
      assertLineIndices(newLine, "", "Hello World!");
      // Test two previous empty line
      assertLineIndices(newLine, "", "", "Hello World!");
      // Test one following empty line
      assertLineIndices(newLine, "Hello World!", "");
      // Test two following empty line
      assertLineIndices(newLine, "Hello World!", "", "");
      // Test one previous and following empty line
      assertLineIndices(newLine, "", "Hello World!", "");
      // Test two previous and following empty line
      assertLineIndices(newLine, "", "", "Hello World!", "", "");
      // Test two previous and following empty line
      assertLineIndices(newLine, "", "", "Hello World!", "", "");
      // Test example documentation
      assertLineIndices(newLine, "Line 1", "Line 2: With some text", "", "Line 4");
   }
   
   /**
    * Constructs a text for the given lines and tests the computed
    * start line indices.
    * @param newLine The new line sign to use.
    * @param textLines The lines of text.
    * @throws IOException Occurred Exception.
    */
   protected void assertLineIndices(String newLine, String... textLines) throws IOException {
      if (textLines != null) {
         StringBuffer sb = new StringBuffer();
         int[] expectedIndices = new int[textLines.length];
         int lastIndex = 0;
         for (int i = 0; i < textLines.length; i++) {
            expectedIndices[i] = lastIndex;
            sb.append(textLines[i]);
            lastIndex += textLines[i].length();
            if (i < textLines.length - 1) {
               sb.append(newLine);
               lastIndex += newLine.length();
            }
         }
         assertLineIndices(sb.length() >= 1 ? sb.toString() : null, expectedIndices);
      }
      else {
         assertLineIndices((String)null, new int[0]);
      }
   }

   /**
    * Makes sure that for the given text the correct line start indices are computed.
    * @param text The text to test.
    * @param expectedIndices The expected line indices.
    * @throws IOException Occurred Exception.
    */
   protected void assertLineIndices(String text, int... expectedIndices) throws IOException {
      Integer[] result = IOUtil.computeLineStartIndices(text != null ? new ByteArrayInputStream(text.getBytes()) : null);
      assertNotNull(text, result);
      assertEquals(text, expectedIndices.length, result.length);
      for (int i = 0; i < expectedIndices.length; i++) {
         assertEquals(text + " at " + i, expectedIndices[i], result[i].intValue());
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
    * Tests {@link IOUtil#readFrom(java.io.InputStream)}
    */
   @Test
   public void testReadFrom() {
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
         assertNull(IOUtil.readFrom(null));
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
       TestUtilsUtil.createFolder(tmpFile);
       IOUtil.delete(tmpFile);
       assertFalse(tmpFile.exists());
       // Test directory with content
       TestUtilsUtil.createFolder(tmpFile);
       File subDir = TestUtilsUtil.createFolder(new File(tmpFile, "subDir"));
       File subFile = TestUtilsUtil.createFile(new File(tmpFile, "subFile.txt"), "test");
       File subDir2 = TestUtilsUtil.createFolder(new File(tmpFile, "subDir"));
       File subSubDir2 = TestUtilsUtil.createFolder(new File(subDir2, "subDir"));
       File subSubSubDir2 = TestUtilsUtil.createFolder(new File(subSubDir2, "subDir"));
       File subSubSubDir2File = TestUtilsUtil.createFile(new File(subSubSubDir2, "subFile.txt"), "test");
       IOUtil.delete(tmpFile);
       assertFalse(tmpFile.exists());
       assertFalse(subDir.exists());
       assertFalse(subFile.exists());
       assertFalse(subDir2.exists());
       assertFalse(subSubDir2.exists());
       assertFalse(subSubSubDir2.exists());
       assertFalse(subSubSubDir2File.exists());
   }
}
