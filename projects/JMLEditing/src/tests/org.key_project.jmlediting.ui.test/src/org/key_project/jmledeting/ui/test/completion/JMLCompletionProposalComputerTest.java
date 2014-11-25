package org.key_project.jmledeting.ui.test.completion;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.List;

import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.junit.Before;
import org.junit.Test;
import org.key_project.jmlediting.ui.test.TestUtils;

public class JMLCompletionProposalComputerTest {

   static SWTWorkbenchBot bot = new SWTWorkbenchBot();
   
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
   
   @Before
   public void prepare() {
      TestUtils.prepareWorkbench(bot);
      TestUtils.createEmptyJavaProject(bot, PROJECT_NAME);
      TestUtils.createEmptyPackage(bot, PACKAGE_NAME);
      TestUtils.createEmptyClass(bot, PACKAGE_NAME, CLASS_NAME);
      bot.activeEditor().toTextEditor().setText(EDITOR_TEXT);
   }
   
   @Test
   public void testCompletion() {
      SWTBotEclipseEditor editor = bot.activeEditor().toTextEditor();
      
      //test in JML Comment
      editor.navigateTo(6, 12);
      List<String> list = editor.getAutoCompleteProposals("");
      assertTrue("Not the correct amount of Proposals", list.size() == 10);
      list = editor.getAutoCompleteProposals("exeption");
      assertTrue("Not the correct amount of Proposals", list.size() == 2);
      list = editor.getAutoCompleteProposals("ensur");
      assertTrue("Not the correct amount of Proposals", list.size() == 1);
      
      //Test in Java Code
      editor.navigateTo(10, 9);
      list = editor.getAutoCompleteProposals("ensu");
      assertFalse("Proposed JML in Java code", list.contains("ensures"));
      
      //Test in Java Comment
      editor.navigateTo(9, 18);
      list = editor.getAutoCompleteProposals("ensu");
      assertFalse("Proposed JML in Java commend", list.contains("ensures"));
      }
}
