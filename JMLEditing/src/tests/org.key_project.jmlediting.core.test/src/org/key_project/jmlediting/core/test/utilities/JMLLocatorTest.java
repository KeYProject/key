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
   private static final String TEXT4 = "/*@" + eol + eol
         + "// random testingstuff" + eol + eol + eol;
   private CommentLocator locator = new CommentLocator(EDITOR_TEXT);

   @Test
   public void findCommentsTest() {
      assertFalse("No JML Comments found", this.locator.findJMLCommentRanges()
            .isEmpty());
      this.locator = new CommentLocator(TEXT2);
      assertFalse("No JML Comments found", this.locator.findJMLCommentRanges()
            .isEmpty());
      this.locator = new CommentLocator(TEXT3);
      assertFalse("No JML Comments found", this.locator.findJMLCommentRanges()
            .isEmpty());
   }

   @Test
   public void isInJMLTest() {
      this.locator = new CommentLocator(EDITOR_TEXT);
      // Test in JML Comment
      assertTrue("Offset should be in JML Comment but result was false",
            this.locator.isInJMLComment(EDITOR_TEXT.indexOf("/*@") + 3));
      // Test in normal Comment
      assertFalse("Offset was wrongly recognized as in a JML Comment",
            this.locator.isInJMLComment(EDITOR_TEXT.indexOf("//") + 3));
      // Test outside a comment
      assertFalse("Offset was wrongly recognized as in a JML Comment",
            this.locator.isInJMLComment(0));
      // Test inside a String
      assertFalse("Offset was wrongly recognized as in a JML Comment",
            this.locator.isInJMLComment(EDITOR_TEXT.indexOf("//@" + 3)));
      // Test in JML Singleline
      assertTrue(
            "Offset was wrongly recognized as not in a JML Comment",
            this.locator.isInJMLComment(EDITOR_TEXT.indexOf("//@",
                  EDITOR_TEXT.indexOf("ensures")) + 1));

   }

   @Test
   public void findJMLCommentsTest() {
      this.locator = new CommentLocator(EDITOR_TEXT);
      List<CommentRange> comments = this.locator.findJMLCommentRanges();
      assertEquals("The expected number of JML Comments was not found", 2,
            comments.size());
      this.locator = new CommentLocator(TEXT2);
      comments = this.locator.findJMLCommentRanges();
      assertEquals("The expected number of JML Comments was not found", 2,
            comments.size());
      this.locator = new CommentLocator(TEXT3);
      comments = this.locator.findJMLCommentRanges();
      assertEquals("The expected number of JML Comments was not found", 2,
            comments.size());
   }

   @Test
   public void getCommentOfOffsetTest() {
      this.locator = new CommentLocator(EDITOR_TEXT);
      List<CommentRange> comments = this.locator.findJMLCommentRanges();
      CommentRange commentToFind = comments.get(0);
      CommentRange commentFound = this.locator.getCommentOfOffset(57);
      assertEquals("Wrong begin offset for surrounding Comment",
            commentToFind.getBeginOffset(), commentFound.getBeginOffset());
      assertEquals("Wrong end offset for surrounding Comment",
            commentToFind.getEndOffset(), commentFound.getEndOffset());
      comments = this.locator.findCommentRanges();
      commentToFind = comments.get(comments.size() - 1);
      commentFound = this.locator.getCommentOfOffset(EDITOR_TEXT.length() - 1);
      assertEquals("Wrong begin offset for surrounding Comment",
            commentToFind.getBeginOffset(), commentFound.getBeginOffset());
      assertEquals("Wrong end offset for surrounding Comment",
            commentToFind.getEndOffset(), commentFound.getEndOffset());
      assertNull(
            "Found surrounding Comment where no surrounding comment should be",
            this.locator.getCommentOfOffset(0));
   }

   @Test
   public void getJMLCommentTest() {
      this.locator = new CommentLocator(EDITOR_TEXT);
      assertNull(
            "Found surrounding JML comment where no JML comment should be",
            this.locator.getJMLComment(EDITOR_TEXT.length() - 1));
      List<CommentRange> comments = this.locator.findCommentRanges();
      final CommentRange commentToFind = comments.get(0);
      final CommentRange commentFound = this.locator.getJMLComment(57);
      assertEquals("Wrong begin offset for surrounding JML Comment",
            commentToFind.getBeginOffset(), commentFound.getBeginOffset());
      assertEquals("Wrong end offset for surrounding JML Comment",
            commentToFind.getEndOffset(), commentFound.getEndOffset());
      this.locator = new CommentLocator(TEXT2);
      comments = this.locator.findCommentRanges();
      assertNull(
            "Found surrounding Comment where no surrounding JML Comment was expected",
            this.locator.getJMLComment(78));
   }

   @Test
   public void indexTest() {
      this.locator = new CommentLocator(EDITOR_TEXT);
      final List<CommentRange> comments = this.locator.findCommentRanges();
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
      this.locator = new CommentLocator(EDITOR_TEXT);
      final List<CommentRange> comments = this.locator.findCommentRanges();
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
      this.locator = new CommentLocator(EDITOR_TEXT);
      final List<CommentRange> comments = this.locator.findJMLCommentRanges();
      assertEquals("Wrong length of first JMLComment", comments.get(0)
            .getLength(), 26);
      assertEquals("Wrong length of second JMLComment", comments.get(1)
            .getLength(), 20);
   }

   @Test
   public void contentLengthTest() {
      this.locator = new CommentLocator(EDITOR_TEXT);
      final List<CommentRange> comments = this.locator.findJMLCommentRanges();
      assertEquals("Wrong length of first JMLComment content", comments.get(0)
            .getContentLength(), 22);
      assertEquals("Wrong length of second JMLComment content", comments.get(1)
            .getContentLength(), 18);
   }

   @Test
   public void openCommentTest() {
      this.locator = new CommentLocator(TEXT4);
      final List<CommentRange> comments = this.locator.findCommentRanges();
      assertEquals("Wrong size of CommentList for OpenComment", 1,
            comments.size());
      assertEquals("Wrong length of Open comment", TEXT4.length(), comments
            .get(0).getLength());
   }
}
