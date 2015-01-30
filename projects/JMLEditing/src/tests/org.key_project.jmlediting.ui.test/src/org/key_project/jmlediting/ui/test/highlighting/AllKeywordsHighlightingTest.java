package org.key_project.jmlediting.ui.test.highlighting;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.swt.finder.utils.Position;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.IToplevelKeyword;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.ui.test.UITestUtils;
import org.key_project.jmlediting.ui.test.UITestUtils.TestProject;
import org.key_project.jmlediting.ui.test.UITestUtils.TestProject.SaveGuarantee;
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper;
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper.ColorProperty;

public class AllKeywordsHighlightingTest {

   private static SWTWorkbenchBot bot = new SWTWorkbenchBot();
   private static IJMLProfile profile;

   private static TestProject project;

   private SWTBotEclipseEditor editor;

   @BeforeClass
   public static void createProject() throws CoreException,
         InterruptedException {
      profile = UITestUtils.findReferenceProfile();
      project = UITestUtils.createProjectWithFile(bot,
            AllKeywordsHighlightingTest.class, SaveGuarantee.NO_SAVE);
      JMLPreferencesHelper.setProjectJMLProfile(project.getProject()
            .getProject(), profile);
   }

   @Before
   public void resetEditor() throws CoreException {
      project.restoreClassAndOpen();
      this.editor = project.getOpenedEditor();
   }

   @Test
   public void testAllKeywordsUsed() throws ParserException {
      final Set<IKeyword> foundKeywords = new HashSet<IKeyword>();

      // Parse all comments and collect all keywords
      for (final IKeywordNode keywordNode : this
            .getAllCommentsKeywordsInEditor()) {
         foundKeywords.add(keywordNode.getKeyword());
      }

      // Check that all keywords of the profile are available
      final Set<IKeyword> missingKeywords = new HashSet<IKeyword>(
            profile.getSupportedKeywords());
      missingKeywords.removeAll(foundKeywords);

      if (missingKeywords.size() != 0) {
         String message = "The following keywords are missing: ";
         for (final IKeyword keyword : missingKeywords) {
            message += keyword.getKeywords().iterator().next() + ", ";
         }
         fail(message);
      }
   }

   @Test
   public void testAllKeywordsHighlighted() throws ParserException {
      for (final IKeywordNode keywordNode : this
            .getAllCommentsKeywordsInEditor()) {
         final int start = keywordNode.getStartOffset();
         final int end = keywordNode.getEndOffset();
         final IKeyword keyword = keywordNode.getKeyword();
         final RGB desiredColor = JMLUiPreferencesHelper
               .getWorkspaceJMLColor(keyword instanceof IToplevelKeyword ? ColorProperty.TOPLEVEL_KEYWORD
                     : ColorProperty.KEYWORD);
         final Position startInEditor = UITestUtils.getLineAndColumn(start,
               this.editor);
         final StyleRange[] styles = this.editor.getStyles(startInEditor.line,
               startInEditor.column, end - start);
         for (final StyleRange style : styles) {
            assertEquals("Wrong color of keyword "
                  + keyword.getKeywords().iterator().next() + " at "
                  + startInEditor, desiredColor, style.foreground.getRGB());
            assertEquals("Keyword not bold at " + startInEditor, SWT.BOLD,
                  style.fontStyle);
         }
      }
   }

   private List<IKeywordNode> getAllCommentsKeywordsInEditor()
         throws ParserException {
      final List<IKeywordNode> nodes = new ArrayList<IKeywordNode>();
      for (final CommentRange comment : new CommentLocator(
            this.editor.getText()).findJMLCommentRanges()) {
         nodes.addAll(Nodes.getAllKeywords(profile.createParser().parse(
               this.editor.getText(), comment)));
      }
      return nodes;
   }

}
