package org.key_project.jmlediting.ui.test.extension;

import static org.junit.Assert.*;

import org.eclipse.jface.text.BadLocationException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.ui.extension.JMLLocator;

public class JMLLocatorTest {
   
private static final String eol = System.getProperty("line.separator");
   
   private static final String PROJECT_NAME = "TestCompletion";
   private static final String PACKAGE_NAME = "jml.test";
   private static final String CLASS_NAME = "TextClass";
   private static final String EDITOR_TEXT = "package " + PACKAGE_NAME + ";" + eol + eol + 
         "public class " + CLASS_NAME + " {" + eol + eol + 
         "//@ requieres"+ eol+
         "\t /*@ " + eol + "\t * " + eol + "\t */" + eol +
         "\tpublic static void main(String[] args) {" + eol +
         "//normal " + eol + "\t" + eol +
         "String temp=\"//@\" ensures \";"+eol+
         "//@ requires blabla"+eol+
         "\t\tSystem.out.println(\"Hello World\");" + eol +
         "\t}" + eol + "}" + eol;
   private JMLLocator locator;
   

   @Before
   public void setup() throws Exception {
      locator = new JMLLocator(EDITOR_TEXT);
      
   }

   @Test
   public void findCommentsTest() {
      assertFalse(locator.findJMLComments().isEmpty());
   }

   @Test
   public void isInJMLTest() throws BadLocationException {
      assertTrue(locator.isInJMLcomment(EDITOR_TEXT.indexOf("/*@")+3));    //Test whether JML Multiline Comment is recognized
      assertFalse(locator.isInJMLcomment(EDITOR_TEXT.indexOf("//")+3));    //Test whether JavaComment is recognized as JMLComment
      assertFalse(locator.isInJMLcomment(0));                              //Test
      //assertFalse(locator.isInJMLcomment(EDITOR_TEXT.indexOf("//@"+3)));   //Test whether JMLComment in String is detected
      assertTrue(locator.isInJMLcomment(EDITOR_TEXT.indexOf("//@")+3));

   }

}
