package org.key_project.jmledeting.ui.test.completion;

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
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.IToplevelKeyword;
import org.key_project.jmlediting.ui.test.Activator;
import org.key_project.jmlediting.ui.test.UITestUtils;
import org.key_project.util.eclipse.BundleUtil;
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
 * <li>"ensu" &lt;- only "ensures" fits</li>
 * <li>"exception" &lt- the two keywords "exceptional_behavior" and
 * "exceptional_behaviour" fit</li>
 * </ul>
 *
 *
 * @author Thomas Glaser
 *
 */
public class JMLCompletionProposalComputerTest {

   static SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private SWTBotEclipseEditor editor = null;

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

   private static final String KEYWORD_ENSURES = "ensures";
   private static final String KEYWORD_EXCEPTIONAL_BEHAVIOR = "exceptional_behavior";
   private static final String INSERTTEXT_NOKEYWORD = "nokeyword";
   private static final String INSERTTEXT_EXCEPTIONAL_BEHAVIOR = "exception";
   private static final String INSERTTEXT_ENSURES = "ensu";

   private static int MAX_KEYWORDS = 0;

   /*
    * Initialize a new Project and load the template class from data/template
    * with all kinds of Comments to test AutoCompletion in and open it.
    */
   @BeforeClass
   public static void initProject() throws CoreException, InterruptedException {
      final IJavaProject project = TestUtilsUtil
            .createJavaProject(PROJECT_NAME);
      final IFolder srcFolder = project.getProject().getFolder("src");
      final IFolder testFolder = TestUtilsUtil.createFolder(srcFolder,
            PACKAGE_NAME);
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID,
            "data/template", testFolder);
      bot.tree().getTreeItem(PROJECT_NAME).select().expand().getNode("src")
            .select().expand().getNode(PACKAGE_NAME).select().expand()
            .getNode(CLASS_NAME + ".java").select().doubleClick();
      bot.sleep(1000);

      final IJMLProfile profile = UITestUtils.findReferenceProfile();
      JMLPreferencesHelper.setProjectJMLProfile(project.getProject(), profile);

      // count MAX_KEYWORDS
      final Set<IKeyword> keywordSet = JMLProfileHelper.filterKeywords(profile,
            IToplevelKeyword.class);
      for (final IKeyword iKeyword : keywordSet) {
         MAX_KEYWORDS += iKeyword.getKeywords().size();
      }
   }

   /*
    * just make sure the global variable editor is set
    */
   @Before
   public void initEditor() {
      this.editor = bot.activeEditor().toTextEditor();
   }

   /*
    * removes the text with given length at Position pos
    */
   private void removeText(final Position pos, final int length) {
      this.editor.selectRange(pos.line, pos.column, length);
      bot.sleep(100);
      this.editor.pressShortcut(Keystrokes.DELETE);
   }

   /*
    * asks for AutoComplete and deletes insertText afterwards
    */
   private List<String> getCompletion(final Position pos,
         final String insertText) {
      this.editor.navigateTo(pos);
      final List<String> proposals = this.editor
            .getAutoCompleteProposals(insertText);
      if (!insertText.isEmpty()) {
         this.removeText(pos, insertText.length());
      }
      bot.sleep(20000);
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
   public void testCompletionJMLCommentSingleEnsures() {
      this.testWithTimeout(PosJMLCommentSingle, INSERTTEXT_ENSURES);
      assertTrue(
            "Not the correct amount of proposals in JML-single-line-comment get ensures proposal",
            this.editor.getTextOnCurrentLine().contains(KEYWORD_ENSURES));
      this.removeText(PosJMLCommentSingle, KEYWORD_ENSURES.length());
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
   public void testCompletionJMLCommentMultiEnsures() {
      this.testWithTimeout(PosJMLCommentMulti, INSERTTEXT_ENSURES);
      assertTrue("Not the correct amount of Proposals", this.editor
            .getTextOnCurrentLine().contains(KEYWORD_ENSURES));
      this.removeText(PosJMLCommentMulti, KEYWORD_ENSURES.length());
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
            proposals.contains(KEYWORD_ENSURES));
   }

   @Test
   public void testCompletionJDocCommentNoJMLProposalsBehavior() {
      final List<String> proposals = this.getCompletion(PosJDocComment,
            INSERTTEXT_EXCEPTIONAL_BEHAVIOR);
      assertFalse("Found JML proposals in JDoc comment",
            proposals.contains(KEYWORD_EXCEPTIONAL_BEHAVIOR));
   }

   @Test
   public void testCompletionJDocCommentNoJMLProposalsEnsures() {
      this.testWithTimeout(PosJDocComment, INSERTTEXT_ENSURES);
      this.removeText(PosJDocComment, INSERTTEXT_ENSURES.length());
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
   public void testCompletionJCommentMultiNoJMLProposalsEnsures() {
      this.testWithTimeout(PosJCommentMulti, INSERTTEXT_ENSURES);
      this.removeText(PosJCommentMulti, INSERTTEXT_ENSURES.length());
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
            proposals.contains(KEYWORD_ENSURES));
   }

   @Test
   public void testCompletionJCommentSingleNoJMLProposalsBehavior() {
      this.testWithTimeout(PosJCommentSingle, INSERTTEXT_EXCEPTIONAL_BEHAVIOR);
      this.removeText(PosJCommentSingle,
            INSERTTEXT_EXCEPTIONAL_BEHAVIOR.length());
   }

   @Test
   public void testCompletionJCommentSingleNoJMLProposalsEnsures() {
      this.testWithTimeout(PosJCommentSingle, INSERTTEXT_ENSURES);
      this.removeText(PosJCommentSingle, INSERTTEXT_ENSURES.length());
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
   public void testCompletionInStringNoJMLProposalsEnsures() {
      this.testWithTimeout(PosInString, INSERTTEXT_ENSURES);
      this.removeText(PosInString, INSERTTEXT_ENSURES.length());
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
            proposals.contains(KEYWORD_ENSURES));
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
   public void testCompletionInMethodNoJMLProposalsEnsures() {
      this.testWithTimeout(PosInMethod, INSERTTEXT_ENSURES);
      this.removeText(PosInMethod, INSERTTEXT_ENSURES.length());
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
            proposals.contains(KEYWORD_ENSURES));
   }

   @Test
   public void testCompletionOutOfClassNoJMLProposalsBehavior() {
      this.testWithTimeout(PosOutOfClass, INSERTTEXT_EXCEPTIONAL_BEHAVIOR);
      this.removeText(PosOutOfClass, INSERTTEXT_EXCEPTIONAL_BEHAVIOR.length());
   }

   @Test
   public void testCompletionOutOfClassNoJMLProposalsEnsures() {
      this.testWithTimeout(PosOutOfClass, INSERTTEXT_ENSURES);
      this.removeText(PosOutOfClass, INSERTTEXT_ENSURES.length());
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
            proposals.contains(KEYWORD_ENSURES));
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
   public void testCompletionInClassNoJMLProposalsEnsures() {
      final List<String> proposals = this.getCompletion(PosInClass,
            INSERTTEXT_ENSURES);
      assertFalse("Found JML proposals in class",
            proposals.contains(KEYWORD_ENSURES));
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
            proposals.contains(KEYWORD_ENSURES)
                  || proposals.contains(KEYWORD_EXCEPTIONAL_BEHAVIOR));
   }
}
