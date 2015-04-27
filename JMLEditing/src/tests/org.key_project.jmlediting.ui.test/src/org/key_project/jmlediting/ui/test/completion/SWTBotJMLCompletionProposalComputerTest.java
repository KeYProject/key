package org.key_project.jmlediting.ui.test.completion;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.swt.finder.keyboard.Keystrokes;
import org.eclipse.swtbot.swt.finder.utils.Position;
import org.eclipse.swtbot.swt.finder.widgets.TimeoutException;
import org.eclipse.ui.IEditorPart;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.ToplevelKeywordSort;
import org.key_project.jmlediting.ui.test.Activator;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Testingplan of JML AutoCompletion:<br/>
 * Test AutoCompletion at every different possible position<br/>
 * <ul>
 * <li>Out of class</li>
 * <li>JDoc comment</li>
 * <li>Multiline Java comment</li>
 * <li>Multiline JML comment</li>
 * <li>In class</li>
 * <li>In string</li>
 * <li>Singleline Java comment</li>
 * <li>In method</li>
 * <li>Singleline JML comment</li>
 * </ul>
 * with keywords:<br/>
 * <ul>
 * <li>"" &lt;- All proposals</li>
 * <li>"nokeyword" &lt;- no proposal</li>
 * <li>"mainta" &lt;- only "maintaining" fits</li>
 * <li>"exception" &lt- the two keywords "exceptional_behavior" and
 * "exceptional_behaviour" fit</li>
 * </ul>
 *
 *
 * @author Thomas Glaser
 *
 */
public class SWTBotJMLCompletionProposalComputerTest {

   private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static SWTBotEclipseEditor editor = null;

   private static final String PROJECT_NAME = "TestCompletion";
   private static final String PACKAGE_NAME = "test";
   private static final String CLASS_NAME = "TestClass";

   // SWTBot uses strange offsets... according to JavaClass
   // data/template/TestClass.java
   private static final Position PosOutOfClass = new Position(3, 0);
   private static final Position PosJDocComment = new Position(6, 23);
   private static final Position PosJCommentMulti = new Position(11, 31);
   private static final Position PosJMLCommentMulti = new Position(14, 18);
   private static final Position PosInClass = new Position(17, 3);
   private static final Position PosInString = new Position(20, 35);
   private static final Position PosJCommentSingle = new Position(20, 89);
   private static final Position PosInMethod = new Position(22, 6);
   private static final Position PosJMLCommentSingle = new Position(23, 28);

   private static final String KEYWORD_MAINTAINING = "maintaining";
   private static final String KEYWORD_EXCEPTIONAL_BEHAVIOR = "exceptional_behavior";
   private static final String INSERTTEXT_NOKEYWORD = "nokeyword";
   private static final String INSERTTEXT_EXCEPTIONAL_BEHAVIOR = "exception";
   private static final String INSERTTEXT_MAINTAINING = "mainta";

   private static int MAX_KEYWORDS = 0;
   
   private static IEditorPart editorPart;

   /*
    * Initialize a new Project and load the template class from data/template
    * with all kinds of Comments to test AutoCompletion in and open it.
    */
   @BeforeClass
   public static void initProject() throws CoreException, InterruptedException {
      TestUtilsUtil.closeWelcomeView();
      final IJavaProject project = TestUtilsUtil.createJavaProject(PROJECT_NAME);
      final IFolder srcFolder = project.getProject().getFolder("src");
      final IFolder testFolder = TestUtilsUtil.createFolder(srcFolder, PACKAGE_NAME);
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/template", testFolder);
      editorPart = TestUtilsUtil.openEditor(testFolder.getFile(CLASS_NAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
      editor = bot.activeEditor().toTextEditor();

      final IJMLProfile profile = JMLEditingUITestUtils.findReferenceProfile();
      JMLPreferencesHelper.setProjectJMLProfile(project.getProject(), profile);

      // count MAX_KEYWORDS
      final Set<IKeyword> keywordSet = JMLProfileHelper.filterKeywords(profile, ToplevelKeywordSort.INSTANCE);
      for (final IKeyword iKeyword : keywordSet) {
         MAX_KEYWORDS += iKeyword.getKeywords().size();
      }
   }
   
   @AfterClass
   public static void closeEditor() {
      TestUtilsUtil.closeEditor(editorPart, false);
   }

   /*
    * removes the text with given length at Position pos
    */
   private void removeText(final Position pos, final int length) {
      editor.selectRange(pos.line, pos.column, length);
      editor.pressShortcut(Keystrokes.DELETE);
   }

   /*
    * asks for AutoComplete and deletes insertText afterwards
    */
   private List<String> getCompletion(final Position pos,
         final String insertText) {
      editor.navigateTo(pos);
      final List<String> proposals = editor
            .getAutoCompleteProposals(insertText);
      if (!insertText.isEmpty()) {
         this.removeText(pos, insertText.length());
      }
      return proposals;
   }

   /*
    * Should lead to a TimeoutException not solved via expected, because
    * inputText must be deleted from caller after this method
    * 
    * Also can have one Proposal containing "No Default Proposals"
    */
   private void testWithTimeout(final Position pos, final String insertText) {
      Boolean gotTimeout = false;
      Boolean gotProposalNoDefaultProposals = false;
      final String nodefaultproposals = "No Default Proposals";
      try {
         final List<String> proposals = this.getCompletion(pos, insertText);
         if (proposals.size() == 1) {
            gotProposalNoDefaultProposals = proposals
                  .contains(nodefaultproposals);
         }
      }
      catch (final TimeoutException toe) {
         gotTimeout = true;
      }
      catch (final Exception e) {
         e.printStackTrace();
         // nothing ToDo here, so assertion fails
      }
      finally {
         assertTrue("got no Timeout, but expected one", gotTimeout
               || gotProposalNoDefaultProposals);
      }
   }

   @Test
   public void testCompletionJMLCommentSingleAll() {
      final List<String> proposals = this
            .getCompletion(PosJMLCommentSingle, "");
      assertTrue(
            "Not the correct amount of proposals in JML-single-line-comment get all proposals",
            proposals.size() == MAX_KEYWORDS + 4); // +4 for default
      // single-line-comment-proposals
      // in java-editor (new, nls,
      // runnable, toarray)
   }

   @Test
   public void testCompletionJMLCommentSingleBehavior() {
      final List<String> proposals = this.getCompletion(PosJMLCommentSingle,
            INSERTTEXT_EXCEPTIONAL_BEHAVIOR);
      assertTrue(
            "Not the correct amount of proposals in JML-single-line-comment get exceptional_behavio(u)r proposals",
            proposals.size() == 2);
   }

   /*
    * direct AutoCompletion without proposal-dialog lets the Method
    * editor.getAutoCompleteProposals throw a TimeoutException
    */
   @Test
   public void testCompletionJMLCommentSingleMaintaining() {
      this.testWithTimeout(PosJMLCommentSingle, INSERTTEXT_MAINTAINING);
      assertTrue(
            "Not the correct amount of proposals in JML-single-line-comment get maintaining proposal",
            editor.getTextOnCurrentLine().contains(KEYWORD_MAINTAINING));
      this.removeText(PosJMLCommentSingle, KEYWORD_MAINTAINING.length());
   }

   @Test
   public void testCompletionJMLCommentSingleNoProposalNoKeyWord() {
      this.testWithTimeout(PosJMLCommentSingle, INSERTTEXT_NOKEYWORD);
      this.removeText(PosJMLCommentSingle, INSERTTEXT_NOKEYWORD.length());
   }

   @Test
   public void testCompletionJMLCommentMultiAll() {
      final List<String> proposals = this.getCompletion(PosJMLCommentMulti, "");
      assertTrue("Not the correct amount of Proposals: " + proposals.size(),
            proposals.size() == MAX_KEYWORDS);
   }

   @Test
   public void testCompletionJMLCommentMultiBehavior() {
      final List<String> proposals = this.getCompletion(PosJMLCommentMulti,
            INSERTTEXT_EXCEPTIONAL_BEHAVIOR);
      assertTrue("Not the correct amount of Proposals", proposals.size() == 2);
   }

   @Test
   public void testCompletionJMLCommentMultiMaintaining() {
      this.testWithTimeout(PosJMLCommentMulti, INSERTTEXT_MAINTAINING);
      assertTrue("Not the correct amount of Proposals", editor
            .getTextOnCurrentLine().contains(KEYWORD_MAINTAINING));
      this.removeText(PosJMLCommentMulti, KEYWORD_MAINTAINING.length());
   }

   @Test
   public void testCompletionJMLCommentMultiNoProposalsNoKeyWord() {
      this.testWithTimeout(PosJMLCommentMulti, INSERTTEXT_NOKEYWORD);
      this.removeText(PosJMLCommentMulti, INSERTTEXT_NOKEYWORD.length());
   }

   @Test
   public void testCompletionJDocCommentNoJMLProposalsAll() {
      final List<String> proposals = this.getCompletion(PosJDocComment, "");
      assertFalse("Found JML proposals in JDoc comment",
            proposals.contains(KEYWORD_MAINTAINING));
   }

   @Test
   public void testCompletionJDocCommentNoJMLProposalsBehavior() {
      final List<String> proposals = this.getCompletion(PosJDocComment,
            INSERTTEXT_EXCEPTIONAL_BEHAVIOR);
      assertFalse("Found JML proposals in JDoc comment",
            proposals.contains(KEYWORD_EXCEPTIONAL_BEHAVIOR));
   }

   @Test
   public void testCompletionJDocCommentNoJMLProposalsMaintaining() {
      this.testWithTimeout(PosJDocComment, INSERTTEXT_MAINTAINING);
      this.removeText(PosJDocComment, INSERTTEXT_MAINTAINING.length());
   }

   @Test
   public void testCompletionJDocCommentNoJMLProposalsNoKeyWord() {
      this.testWithTimeout(PosJDocComment, INSERTTEXT_NOKEYWORD);
      this.removeText(PosJDocComment, INSERTTEXT_NOKEYWORD.length());
   }

   @Test
   public void testCompletionJCommentMultiNoJMLProposalsAll() {
      this.testWithTimeout(PosJCommentMulti, "");
   }

   @Test
   public void testCompletionJCommentMultiNoJMLPoposalsBehavior() {
      this.testWithTimeout(PosJCommentMulti, INSERTTEXT_EXCEPTIONAL_BEHAVIOR);
      this.removeText(PosJCommentMulti,
            INSERTTEXT_EXCEPTIONAL_BEHAVIOR.length());
   }

   @Test
   public void testCompletionJCommentMultiNoJMLProposalsMaintaining() {
      this.testWithTimeout(PosJCommentMulti, INSERTTEXT_MAINTAINING);
      this.removeText(PosJCommentMulti, INSERTTEXT_MAINTAINING.length());
   }

   @Test
   public void testCompletionJCommentMultiNoJMLProposalsNoKeyWord() {
      this.testWithTimeout(PosJCommentMulti, INSERTTEXT_NOKEYWORD);
      this.removeText(PosJCommentMulti, INSERTTEXT_NOKEYWORD.length());
   }

   @Test
   public void testCompletionJCommentSingleNoJMLProposalsAll() {
      final List<String> proposals = this.getCompletion(PosJCommentSingle, "");
      assertFalse("Found JML proposals in Java-single-line-comment",
            proposals.contains(KEYWORD_MAINTAINING));
   }

   @Test
   public void testCompletionJCommentSingleNoJMLProposalsBehavior() {
      this.testWithTimeout(PosJCommentSingle, INSERTTEXT_EXCEPTIONAL_BEHAVIOR);
      this.removeText(PosJCommentSingle,
            INSERTTEXT_EXCEPTIONAL_BEHAVIOR.length());
   }

   @Test
   public void testCompletionJCommentSingleNoJMLProposalsMaintaining() {
      this.testWithTimeout(PosJCommentSingle, INSERTTEXT_MAINTAINING);
      this.removeText(PosJCommentSingle, INSERTTEXT_MAINTAINING.length());
   }

   @Test
   public void testCompletionJCommentSingleNoJMLProposalsNoKeyWord() {
      this.testWithTimeout(PosJCommentSingle, INSERTTEXT_NOKEYWORD);
      this.removeText(PosJCommentSingle, INSERTTEXT_NOKEYWORD.length());
   }

   @Test
   public void testCompletionInStringNoJMLProposalsAll() {
      this.testWithTimeout(PosInString, "");
   }

   @Test
   public void testCompletionInStringNoJMLProposalsBehavior() {
      this.testWithTimeout(PosInString, INSERTTEXT_EXCEPTIONAL_BEHAVIOR);
      this.removeText(PosInString, INSERTTEXT_EXCEPTIONAL_BEHAVIOR.length());
   }

   @Test
   public void testCompletionInStringNoJMLProposalsMaintaining() {
      this.testWithTimeout(PosInString, INSERTTEXT_MAINTAINING);
      this.removeText(PosInString, INSERTTEXT_MAINTAINING.length());
   }

   @Test
   public void testCompletionInStringNoJMLProposalsNoKeyWord() {
      this.testWithTimeout(PosInString, INSERTTEXT_NOKEYWORD);
      this.removeText(PosInString, INSERTTEXT_NOKEYWORD.length());
   }

   @Test
   public void testCompletionInMethodNoJMLProposalsAll() {
      final List<String> proposals = this.getCompletion(PosInMethod, "");
      assertFalse("Found JML proposals in Java-code",
            proposals.contains(KEYWORD_MAINTAINING));
   }

   /*
    * insertText "exception" gets proposals in method, but no JML proposals
    */
   @Test
   public void testCompletionInMethodNoJMLProposalsBehavior() {
      final List<String> proposals = this.getCompletion(PosInMethod,
            INSERTTEXT_EXCEPTIONAL_BEHAVIOR);
      assertFalse("Found JML proposals in Java-code",
            proposals.contains(KEYWORD_EXCEPTIONAL_BEHAVIOR));
   }

   @Test
   public void testCompletionInMethodNoJMLProposalsMaintaining() {
      this.testWithTimeout(PosInMethod, INSERTTEXT_MAINTAINING);
      this.removeText(PosInMethod, INSERTTEXT_MAINTAINING.length());
   }

   @Test
   public void testCompletionInMethodNoJMLProposalsNoKeyWord() {
      this.testWithTimeout(PosInMethod, INSERTTEXT_NOKEYWORD);
      this.removeText(PosInMethod, INSERTTEXT_NOKEYWORD.length());
   }

   @Test
   public void testCompletionOutOfClassNoJMLProposalsAll() {
      final List<String> proposals = this.getCompletion(PosOutOfClass, "");
      assertFalse("Found JML proposals out of class",
            proposals.contains(KEYWORD_MAINTAINING));
   }

   @Test
   public void testCompletionOutOfClassNoJMLProposalsBehavior() {
      this.testWithTimeout(PosOutOfClass, INSERTTEXT_EXCEPTIONAL_BEHAVIOR);
      this.removeText(PosOutOfClass, INSERTTEXT_EXCEPTIONAL_BEHAVIOR.length());
   }

   @Test
   public void testCompletionOutOfClassNoJMLProposalsMaintaining() {
      this.testWithTimeout(PosOutOfClass, INSERTTEXT_MAINTAINING);
      this.removeText(PosOutOfClass, INSERTTEXT_MAINTAINING.length());
   }

   @Test
   public void testCompletionOutOfClassNoJMLProposalsNoKeyWord() {
      this.testWithTimeout(PosOutOfClass, INSERTTEXT_NOKEYWORD);
      this.removeText(PosOutOfClass, INSERTTEXT_NOKEYWORD.length());
   }

   @Test
   public void testCompletionInClassNoJMLProposalsAll() {
      final List<String> proposals = this.getCompletion(PosInClass, "");
      assertFalse("Found JML proposals in class",
            proposals.contains(KEYWORD_MAINTAINING));
   }

   @Test
   public void testCompletionInClassNoJMLProposalsBehavior() {
      final List<String> proposals = this.getCompletion(PosInClass,
            INSERTTEXT_EXCEPTIONAL_BEHAVIOR);
      assertFalse("Found JML proposals in class",
            proposals.contains(KEYWORD_EXCEPTIONAL_BEHAVIOR));
   }

   /*
    * In class all inputs get a proposal to form a method with this inputText
    */
   @Test
   public void testCompletionInClassNoJMLProposalsMaintaining() {
      final List<String> proposals = this.getCompletion(PosInClass,
            INSERTTEXT_MAINTAINING);
      assertFalse("Found JML proposals in class",
            proposals.contains(KEYWORD_MAINTAINING));
   }

   /*
    * In class all inputs get a proposal to form a method with this inputText
    */
   @Test
   public void testCompletionInClassNoJMLProposalsNoKeyWord() {
      final List<String> proposals = this.getCompletion(PosInClass,
            INSERTTEXT_NOKEYWORD);
      assertFalse(
            "Found JML proposals in class",
            proposals.contains(KEYWORD_MAINTAINING)
                  || proposals.contains(KEYWORD_EXCEPTIONAL_BEHAVIOR));
   }
}
