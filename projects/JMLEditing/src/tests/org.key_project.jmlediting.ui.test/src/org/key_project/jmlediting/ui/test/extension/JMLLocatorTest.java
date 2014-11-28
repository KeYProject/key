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
         "\t /*@ blabla *x " + eol + "\t * " + eol + "\t */" + eol +
         "\tpublic static void main(String[] args) {" + eol +
         "//normal " + eol + "\t" + eol +
         "Char x= \'bjkb \\' \'"+eol+
         "String temp=\"//@ ensures \\ \" ;"+eol+
         "//@ requires blabla"+eol+
         "\t\tSystem.out.println(\"Hello World\");" + eol +
         "\t}" + eol + "}" + eol+"//";
   private static final String TEXT2 = "package " + PACKAGE_NAME + ";" + eol + eol + 
         "public class " + CLASS_NAME + " {" + eol + eol +
         "\t /*@ blabla *x " + eol + "\t * " + eol + "\t */" + eol +
         "\tpublic static void main(String[] args) {" + eol +
         "//normal " + eol + "\t" + eol +
         "Char x= \'bjkb \\' \'"+eol+
         "/a"+eol+
         "String temp=\"//@ ensures \\ \" ;"+eol+
         "//@ requires blabla"+eol+
         "\t\tSystem.out.println(\"Hello World\");" + eol +
         "\t}" + eol + "}" + eol+"/";
   private static final String TEXT3 = "package " + PACKAGE_NAME + ";" + eol + eol + 
         "public class " + CLASS_NAME + " {" + eol + eol +
         "\t /*@ blabla *x " + eol + "\t * " + eol + "\t */" + eol +
         "\tpublic static void main(String[] args) {" + eol +
         "//normal " + eol + "\t" + eol +
         "Char x= \'bjkb \\' \'"+eol+
         "/a"+eol+
         "String temp=\"//@ ensures \\ \" ;"+eol+
         "//@ requires blabla"+eol+
         "\t\tSystem.out.println(\"Hello World\");" + eol +
         "\t}" + eol + "}" + eol+"/*   *";
   private JMLLocator locator= new JMLLocator(EDITOR_TEXT);
         
   @Test
   public void findCommentsTest() {
      assertFalse(locator.findJMLComments().isEmpty());
      locator= new JMLLocator(TEXT2);
      assertFalse(locator.findJMLComments().isEmpty());
      locator= new JMLLocator(TEXT3);
      assertFalse(locator.findJMLComments().isEmpty());
   }

   @Test
   public void isInJMLTest() throws BadLocationException {
      locator=new JMLLocator(EDITOR_TEXT);
      assertTrue(locator.isInJMLcomment(EDITOR_TEXT.indexOf("/*@")+3));    //Test whether JML Multiline Comment is recognized
      assertFalse(locator.isInJMLcomment(EDITOR_TEXT.indexOf("//")+3));    //Test whether JavaComment is recognized as JMLComment
      assertFalse(locator.isInJMLcomment(0));                              //Test
      assertFalse(locator.isInJMLcomment(EDITOR_TEXT.indexOf("//@"+3)));   //Test whether JMLComment in String is detected
      assertTrue(locator.isInJMLcomment(EDITOR_TEXT.indexOf("//@",EDITOR_TEXT.indexOf("ensures"))+1));

   }

}
