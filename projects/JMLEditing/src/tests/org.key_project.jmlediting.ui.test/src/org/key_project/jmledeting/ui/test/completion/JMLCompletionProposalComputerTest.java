package org.key_project.jmledeting.ui.test.completion;

import static org.junit.Assert.assertTrue;

import java.util.List;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.swt.finder.keyboard.Keystrokes;
import org.eclipse.swtbot.swt.finder.utils.Position;
import org.eclipse.swtbot.swt.finder.widgets.TimeoutException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.ui.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class JMLCompletionProposalComputerTest {

   static SWTWorkbenchBot bot = new SWTWorkbenchBot();
   
   private SWTBotEclipseEditor editor = null;
   
   private static final String PROJECT_NAME = "TestCompletion";
   private static final String PACKAGE_NAME = "test";
   private static final String CLASS_NAME = "TestClass";
   
   //SWTBot uses strange offsets...
   private static final Position PosJDocComment = new Position(5-1, 24-1);
   private static final Position PosJCommentMulti = new Position(10-1, 32-1);
   private static final Position PosJMLCommentMulti = new Position(13-1, 19-1);
   private static final Position PosInString = new Position(17-1, 36-1);
   private static final Position PosJCommentSingle = new Position(17-1, 90); //without -1... weird
   private static final Position PosJCode = new Position(19-1, 7-1);
   private static final Position PosJMLCommentSingle = new Position(20-1, 29-1);
   
   private static final String ENSURES_KEYWORD = "ensures";
   
   private static final int Max_Keywords = 10;
   
   /*
    * Initialize a new Project and load the template class from data/template with all kinds of Comments to test
    * AutoCompletion in and open it.
    */
   @BeforeClass
   public static void initProject() throws CoreException, InterruptedException {
      IJavaProject project = TestUtilsUtil.createJavaProject(PROJECT_NAME);
      IFolder srcFolder = project.getProject().getFolder("src");
      IFolder testFolder = TestUtilsUtil.createFolder(srcFolder, PACKAGE_NAME);
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/template", testFolder);
      bot.tree().getTreeItem(PROJECT_NAME).select().expand().getNode("src").select().expand().getNode(PACKAGE_NAME).select().expand().getNode(CLASS_NAME + ".java").select().doubleClick();
      bot.sleep(1000);
   }
   
   /*
    * just make sure the global variable editor is set
    */
   @Before
   public void initEditor() {
      editor = bot.activeEditor().toTextEditor(); 
   }
   
   /*
    * removes the text with given length at Position pos
    */
   private void removeText(Position pos, int length) {
      editor.selectRange(pos.line,
            pos.column, length);
      bot.sleep(100);
      editor.pressShortcut(Keystrokes.DELETE);
   }
   
   /*
    * asks for AutoComplete and deletes insertText afterwards
    */
   private List<String> getCompletion(Position pos, String insertText) {
      editor.navigateTo(pos);
      List<String> list = editor.getAutoCompleteProposals(insertText);
      if (!insertText.isEmpty()) {
         removeText(pos, insertText.length());
      }

      return list;
   }
   
   /*
    * Should lead to a TimeoutException
    * not solved via expected, because inputText must be deleted from caller at the end
    */
   private void testWithTimeout(Position pos, String insertText) {
      Boolean gotTimeout = false;
      try {
         getCompletion(pos, insertText);
      }
      catch (TimeoutException toe) {
         gotTimeout = true;
      }
      catch (Exception e) {
         //nothing ToDo here, so assertion Fails
      } finally {
         assertTrue("not Right Exception was thrown", gotTimeout);
      }
   }
   
   @Test
   public void testCompletionJMLCommentSingleAll() {
      List<String> list = getCompletion(PosJMLCommentSingle, "");
      assertTrue("Not the correct amount of Proposals", list.size() == Max_Keywords+4); //+4 for default single-line-comment-proposals in java-editor (new, nls, runnable, toarray)
   }
   
   @Test
   public void testCompletionJMLCommentSingleBehavior() {
      List<String> list = getCompletion(PosJMLCommentSingle, "exception");
      assertTrue("Not the correct amount of Proposals", list.size() == 2);
   }
   
   @Test
   public void testCompletionJMLCommentSingleEnsures() {
      testWithTimeout(PosJMLCommentSingle, "ensur");
      assertTrue("Not the correct amount of Proposals", editor.getTextOnCurrentLine().contains(ENSURES_KEYWORD));
      removeText(PosJMLCommentSingle, ENSURES_KEYWORD.length());      
   }
   
   @Test
   public void testCompletionJMLCommentSingleNoProposal() {
      String nokeyword = "nokeyword";
      testWithTimeout(PosJMLCommentSingle, nokeyword);
      removeText(PosJMLCommentSingle, nokeyword.length());
   }
   @Test
   public void testCompletionJMLCommentMultiAll() {
      List<String> list = getCompletion(PosJMLCommentMulti, "");
      assertTrue("Not the correct amount of Proposals: " + list.size(), list.size() == Max_Keywords);
   }

   @Test
   public void testCompletionJMLCommentMultiBehavior() {
      List<String> list = getCompletion(PosJMLCommentMulti, "exception");
      assertTrue("Not the correct amount of Proposals", list.size() == 2);
   }
   
   @Test
   public void testCompletionJMLCommentMultiEnsures() {
      testWithTimeout(PosJMLCommentMulti, "ensur");
      assertTrue("Not the correct amount of Proposals", editor.getTextOnCurrentLine().contains(ENSURES_KEYWORD));
      removeText(PosJMLCommentMulti, ENSURES_KEYWORD.length());      
   }
   
   @Test
   public void testCompletionJMLCommentMultiNoProposal() {
      String nokeyword = "nokeyword";
      testWithTimeout(PosJMLCommentMulti, nokeyword);
      removeText(PosJMLCommentMulti, nokeyword.length());
   }
   
//   @Test
//   public void testCompletionJDocComment() {
//      
//   }
//      //test in JML comment
//      editor.navigateTo(6, 12);
//      List<String> list = editor.getAutoCompleteProposals("");          //list all proposals
//      assertTrue("Not the correct amount of Proposals", list.size() == 10);
//      list = editor.getAutoCompleteProposals("exception");               //list proposals for "exceptional_behavior" and "exceptional_behaviour"
//      assertTrue("Not the correct amount of Proposals", list.size() == 2);
//      list = editor.getAutoCompleteProposals("ensur");                  //list proposal for "ensures"
//      assertTrue("Not the correct amount of Proposals", list.size() == 1);
//      
//      //Test in Java code
//      editor.navigateTo(10, 9);
//      list = editor.getAutoCompleteProposals("ensu");                   //should not find any proposal for "ensu" in Java code
//      assertFalse("Proposed JML in Java code", list.contains("ensures"));
//      
//      //Test in Java comment
//      editor.navigateTo(9, 18);
//      list = editor.getAutoCompleteProposals("ensu");                   //should not find any proposal for "ensu" in Java comment
//      assertFalse("Proposed JML in Java commend", list.contains("ensures"));
//      }
}
