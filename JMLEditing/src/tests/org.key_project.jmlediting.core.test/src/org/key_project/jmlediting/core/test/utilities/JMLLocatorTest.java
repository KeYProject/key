package org.key_project.jmlediting.core.test.utilities;

import static org.junit.Assert.*;

import java.util.List;

import org.junit.Test;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;

public class JMLLocatorTest {

   private static final String eol = " \n";

   private static final String PACKAGE_NAME = "jml.test";
   private static final String CLASS_NAME = "TextClass";
   private static final String EDITOR_TEXT = "package " + PACKAGE_NAME + ";"
         + eol + eol + "public class " + CLASS_NAME + " {" + eol + eol
         /* 49 */+ "\t /*@ blabla *x " + eol + "\t * " + eol + "\t */" + eol
         /* 78 */+ "\tpublic static void main(String[] args) {" + eol
         + "//normal "
         /* 130 */+ eol + "\t" + eol + "Char x= \'bjkb \\' \'" + eol
         /* 155 */+ "String temp=\"//@ ensures \\ \" ;" + eol
         /* 187 */+ "//@ requires blabla" + eol
         /* 208 */+ "\t\tSystem.out.println(\"Hello World\");" + eol + "\t}"
         + eol + "}" + eol + "//";
   private static final String TEXT2 = "package " + PACKAGE_NAME + ";" + eol
         + eol + "public class " + CLASS_NAME + " {" + eol + eol
         + "\t /*@ blabla *x " + eol + "\t * " + eol + "\t */" + eol
         + "\tpublic static void main(String[] args) {" + eol + "//normal "
         + eol + "\t" + eol + "Char x= \'bjkb \\' \'" + eol + "/a" + eol
         + "String temp=\"//@ ensures \\ \" ;" + eol + "//@ requires blabla"
         + eol + "\t\tSystem.out.println(\"Hello World\");" + eol + "\t}" + eol
         + "}" + eol + "/";
   private static final String TEXT3 = "package " + PACKAGE_NAME + ";" + eol
         + eol + "public class " + CLASS_NAME + " {" + eol + eol
         + "\t /*@ blabla *x " + eol + "\t * " + eol + "\t */" + eol
         + "\tpublic static void main(String[] args) {" + eol + "//normal "
         + eol + "\t" + eol + "Char x= \'bjkb \\' \'" + eol + "/a" + eol
         + "String temp=\"//@ ensures \\ \" ;" + eol + "//@ requires blabla"
         + eol + "\t\tSystem.out.println(\"Hello World\");" + eol + "\t}" + eol
         + "}" + eol + "/*   *";

   @Test
   public void findCommentsTest() {
      
      assertFalse("No JML Comments found", CommentLocator.listJMLCommentRanges(EDITOR_TEXT)
            .isEmpty());
      assertFalse("No JML Comments found", CommentLocator.listJMLCommentRanges(TEXT2)
            .isEmpty());
      assertFalse("No JML Comments found", CommentLocator.listJMLCommentRanges(TEXT3)
            .isEmpty());
   }

   @Test
   public void isInJMLTest() {
      // Test in JML Comment
      assertTrue("Offset should be in JML Comment but result was false",
            CommentLocator.isJMLComment(EDITOR_TEXT, EDITOR_TEXT.indexOf("/*@")));
      // Test in normal Comment
      assertFalse("Offset was wrongly recognized as in a JML Comment",
            CommentLocator.isJMLComment(EDITOR_TEXT, EDITOR_TEXT.indexOf("//")));
      // Test outside a comment
      assertFalse("Offset was wrongly recognized as in a JML Comment",
            CommentLocator.isJMLComment(EDITOR_TEXT, 0));
      // Test in JML Singleline
      assertTrue(
            "Offset was wrongly recognized as not in a JML Comment",
            CommentLocator.isJMLComment(EDITOR_TEXT, EDITOR_TEXT.indexOf("//@")));

   }

   @Test
   public void findJMLCommentsTest() {
      List<CommentRange> comments = CommentLocator.listJMLCommentRanges(EDITOR_TEXT);
      assertEquals("The expected number of JML Comments was not found", 2,
            comments.size());
      comments = CommentLocator.listJMLCommentRanges(TEXT2);
      assertEquals("The expected number of JML Comments was not found", 2,
            comments.size());
      comments = CommentLocator.listJMLCommentRanges(TEXT3);
      assertEquals("The expected number of JML Comments was not found", 2,
            comments.size());
   }

   @Test
   public void indexTest() {
      final List<CommentRange> comments = CommentLocator.listCommentRanges(EDITOR_TEXT);
      assertEquals("Begin of first Comment did not Match the Expectation",
            EDITOR_TEXT.indexOf("/*@"), comments.get(0).getBeginOffset());
      assertEquals("End of first Comment did not Match the Expectation",
            EDITOR_TEXT.indexOf("*/") + 1, comments.get(0).getEndOffset());
      assertEquals("Wrong begin offset for single line comment",
            EDITOR_TEXT.indexOf("//", 78), comments.get(1).getBeginOffset());
      assertEquals("Wrong end offset for single line comment",
            EDITOR_TEXT.indexOf(eol, 130), comments.get(1).getEndOffset());
      assertEquals("Wrong begin offset for single line comment",
            EDITOR_TEXT.indexOf("//", 187), comments.get(2).getBeginOffset());
      assertEquals("Wrong end offset for single line comment",
            EDITOR_TEXT.indexOf(eol, 188), comments.get(2).getEndOffset());
      assertEquals("Wrong begin offset for single line comment",
            EDITOR_TEXT.indexOf("//", 208), comments.get(3).getBeginOffset());
      assertEquals("Wrong end offset for single line comment",
            EDITOR_TEXT.length() - 1, comments.get(3).getEndOffset());
   }

   @Test
   public void contentOffsetTest() {
      final List<CommentRange> comments = CommentLocator.listCommentRanges(EDITOR_TEXT);
      assertEquals("Begin of first Comment did not Match the Expectation",
            EDITOR_TEXT.indexOf("/*@") + 2, comments.get(0)
                  .getContentBeginOffset());
      assertEquals("End of first Comment did not Match the Expectation",
            EDITOR_TEXT.indexOf("*/") - 1, comments.get(0)
                  .getContentEndOffset());
      assertEquals("Wrong begin offset for single line comment",
            EDITOR_TEXT.indexOf("//", 78) + 2, comments.get(1)
                  .getContentBeginOffset());
      assertEquals("Wrong end offset for single line comment",
            EDITOR_TEXT.indexOf(eol, 130), comments.get(1)
                  .getContentEndOffset());
      assertEquals("Wrong begin offset for single line comment",
            EDITOR_TEXT.indexOf("//", 187) + 2, comments.get(2)
                  .getContentBeginOffset());
      assertEquals("Wrong end offset for single line comment",
            EDITOR_TEXT.indexOf(eol, 188), comments.get(2)
                  .getContentEndOffset());
      assertEquals("Wrong begin offset for single line comment",
            EDITOR_TEXT.indexOf("//", 208) + 2, comments.get(3)
                  .getContentBeginOffset());
      assertEquals("Wrong end offset for single line comment",
            EDITOR_TEXT.length() - 1, comments.get(3).getContentEndOffset());
   }

   @Test
   public void commentLengthTest() {
      final List<CommentRange> comments = CommentLocator.listJMLCommentRanges(EDITOR_TEXT);
      assertEquals("Wrong length of first JMLComment", comments.get(0)
            .getLength(), 26);
      assertEquals("Wrong length of second JMLComment", comments.get(1)
            .getLength(), 20);
   }

   @Test
   public void contentLengthTest() {
      final List<CommentRange> comments = CommentLocator.listJMLCommentRanges(EDITOR_TEXT);
      assertEquals("Wrong length of first JMLComment content", comments.get(0)
            .getContentLength(), 22);
      assertEquals("Wrong length of second JMLComment content", comments.get(1)
            .getContentLength(), 18);
   }
}
