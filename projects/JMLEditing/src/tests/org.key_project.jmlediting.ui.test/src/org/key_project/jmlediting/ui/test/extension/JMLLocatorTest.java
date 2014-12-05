package org.key_project.jmlediting.ui.test.extension;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.util.List;

import org.eclipse.jface.text.BadLocationException;
import org.junit.Test;
import org.key_project.jmlediting.ui.extension.JMLCommentRange;
import org.key_project.jmlediting.ui.extension.JMLLocator;

public class JMLLocatorTest {

   private static final String eol = System.getProperty("line.separator");

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
   private JMLLocator locator = new JMLLocator(EDITOR_TEXT);

   @Test
   public void isInJMLTest() throws BadLocationException {
      this.locator = new JMLLocator(EDITOR_TEXT);
      assertTrue(this.locator.isInJMLcomment(EDITOR_TEXT.indexOf("/*@") + 3)); // Test
      // whether
      // JML
      // Multiline
      // Comment
      // is
      // recognized
      assertFalse(this.locator.isInJMLcomment(EDITOR_TEXT.indexOf("//") + 3)); // Test
      // whether
      // JavaComment
      // is
      // recognized
      // as
      // JMLComment
      assertFalse(this.locator.isInJMLcomment(0)); // Test
      assertFalse(this.locator.isInJMLcomment(EDITOR_TEXT.indexOf("//@" + 3))); // Test
      // whether
      // JMLComment
      // in
      // String
      // is
      // detected
      assertTrue(this.locator.isInJMLcomment(EDITOR_TEXT.indexOf("//@",
            EDITOR_TEXT.indexOf("ensures")) + 1));

   }

   @Test
   public void findJMLCommentsTest() {
      this.locator = new JMLLocator(EDITOR_TEXT);
      List<JMLCommentRange> comments = this.locator.findJMLComments();
      assertTrue(2 == comments.size());
      this.locator = new JMLLocator(TEXT2);
      comments = this.locator.findJMLComments();
      assertTrue(2 == comments.size());
      this.locator = new JMLLocator(TEXT3);
      comments = this.locator.findJMLComments();
      assertTrue(2 == comments.size());
   }

   @Test
   public void getJMLCommentTest() {
      this.locator = new JMLLocator(EDITOR_TEXT);
      assertNull(this.locator.getJMLComment(EDITOR_TEXT.length() - 1));
      List<JMLCommentRange> comments = this.locator.findJMLComments();
      final JMLCommentRange commentToFind = comments.get(0);
      final JMLCommentRange commentFound = this.locator.getJMLComment(57);
      assertTrue(commentToFind.getBeginOffset() == commentFound
            .getBeginOffset()
            && commentToFind.getEndOffset() == commentFound.getEndOffset());
      this.locator = new JMLLocator(TEXT2);
      comments = this.locator.findJMLComments();
      assertNull(this.locator.getJMLComment(78));
   }

   @Test
   public void indexTest() {
      this.locator = new JMLLocator(EDITOR_TEXT);
      final List<JMLCommentRange> comments = this.locator.findJMLComments();
      assertTrue(EDITOR_TEXT.indexOf("/*@") == comments.get(0).getBeginOffset()
            && EDITOR_TEXT.indexOf("*/") + 1 == comments.get(0).getEndOffset());
      assertTrue(EDITOR_TEXT.indexOf("//", 187) == comments.get(1)
            .getBeginOffset()
            && EDITOR_TEXT.indexOf(eol, 188) - 1 == comments.get(1)
            .getEndOffset());
   }

}
