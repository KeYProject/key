package org.key_project.util.test.testcase;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.util.java.IOUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for {@link IOUtil}
 * @author Martin Hentschel
 */
public class IOUtilTest extends TestCase {
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
