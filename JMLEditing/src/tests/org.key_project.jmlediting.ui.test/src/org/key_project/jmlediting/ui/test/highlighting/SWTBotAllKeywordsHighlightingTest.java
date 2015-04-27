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
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.ToplevelKeywordSort;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils.TestProject;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils.TestProject.SaveGuarantee;
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper;
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper.ColorProperty;
import org.key_project.util.test.util.TestUtilsUtil;

public class SWTBotAllKeywordsHighlightingTest {

   private static SWTWorkbenchBot bot = new SWTWorkbenchBot();
   private static IJMLProfile profile;

   private static TestProject project;

   private static SWTBotEclipseEditor editor;

   @BeforeClass
   public static void createProject() throws CoreException, InterruptedException {
      TestUtilsUtil.closeWelcomeView();
      profile = JMLEditingUITestUtils.findReferenceProfile();
      project = JMLEditingUITestUtils.createProjectWithFile(bot, 
                                                            "SWTBotAllKeywordsHighlightingTest", 
                                                            "org.key_project.jmlediting.ui.test.highlighting", 
                                                            "AllKeywordsHighlightingTest", 
                                                            SaveGuarantee.NO_SAVE);
      JMLPreferencesHelper.setProjectJMLProfile(project.getProject().getProject(), profile);
   }

   @Before
   public void resetEditor() throws CoreException {
      project.restoreClassAndOpen();
      editor = project.getOpenedEditor();
   }
   
   @AfterClass
   public static void closeEditor() {
      editor.close();
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
            message += keyword.getKeywords().iterator().next() + "("
                  + keyword.getClass().getName() + "), ";
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
               .getWorkspaceJMLColor(ToplevelKeywordSort.INSTANCE
                     .covers(keyword.getSort()) ? ColorProperty.TOPLEVEL_KEYWORD
                     : ColorProperty.KEYWORD);
         final Position startInEditor = JMLEditingUITestUtils.getLineAndColumn(start,
               editor);
         final StyleRange[] styles = editor.getStyles(startInEditor.line,
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
      for (final CommentRange comment : JMLEditingUITestUtils
            .getAllJMLCommentsInEditor(editor)) {
         nodes.addAll(Nodes.getAllKeywords(profile.createParser().parse(
               editor.getText(), comment)));
      }
      return nodes;
   }

}
