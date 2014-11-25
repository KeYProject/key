package org.key_project.jmlediting.ui.test.extension;

import static org.junit.Assert.*;

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
         "\t /*@ " + eol + "\t * " + eol + "\t */" + eol +
         "\tpublic static void main(String[] args) {" + eol +
         "//normal " + eol + "\t" + eol +
         "\t\tSystem.out.println(\"Hello World\");" + eol +
         "\t}" + eol + "}" + eol;
   private JMLLocator locator;
   

   @Before
   public void setup() throws Exception {
      locator = new JMLLocator(EDITOR_TEXT);
      
   }

   @Test
   public void test() {
      fail("Not yet implemented");
   }

   @Test
   public void findCommentsTest() {
      assertFalse(locator.findJMLComments().isEmpty());
   }

   @Test
   public void isInJMLTest() {

   }

}
