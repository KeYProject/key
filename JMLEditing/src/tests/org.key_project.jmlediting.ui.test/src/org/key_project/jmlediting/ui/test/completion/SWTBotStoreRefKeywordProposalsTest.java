package org.key_project.jmlediting.ui.test.completion;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.swt.finder.utils.Position;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.swtbot.swt.finder.widgets.TimeoutException;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefKeywordSort;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils.TestProject;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils.TestProject.SaveGuarantee;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class SWTBotStoreRefKeywordProposalsTest {

   private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static TestProject project;
   private static SWTBotEclipseEditor editor;
   private static List<Integer> testPositions;

   @BeforeClass
   public static void createProject() throws CoreException, InterruptedException, IOException {
      TestUtilsUtil.closeWelcomeView();
      project = JMLEditingUITestUtils.createProjectWithFile(bot, 
                                                  "StoreRefKeywordProposals", 
                                                  SWTBotStoreRefKeywordProposalsTest.class.getPackage().getName(), 
                                                  "VectorTest", 
                                                  "data/template/storerefproposals/", 
                                                  SaveGuarantee.NO_SAVE);
      JMLPreferencesHelper.setProjectJMLProfile(project.getProject().getProject(), JMLEditingUITestUtils.findReferenceProfile());
      project.restoreClassAndOpen();
      // Preprocess file
      // There are markers following the template [[<num>]] in the text with
      // increasing numbers
      // Remove them and store the positions
      final IFile classFile = project
            .getProject()
            .getProject()
            .getFile(
                  "src/" + project.getPackageName().replace('.', '/') + "/"
                        + project.getClassName() + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT);

      // Read the file
      final BufferedReader reader = new BufferedReader(new InputStreamReader(
            classFile.getContents()));
      String text = "";
      String temp;
      while ((temp = reader.readLine()) != null) {
         text += "\n" + temp;
      }

      // Find and remove the positions
      testPositions = new ArrayList<Integer>();
      int i = 1;
      int offset;

      while ((offset = text.indexOf(getMarker(i))) != -1) {
         text = text.substring(0, offset)
               + text.substring(offset + getMarker(i).length(), text.length());
         testPositions.add(offset);
         i++;
      }

      // Store the transformed file
      classFile.setContents(new ByteArrayInputStream(text.getBytes()),
            IFile.FORCE, null);

   }

   private static String getMarker(final int i) {
      return "[[" + i + "]]";
   }

   @Before
   public void cleanEditor() throws CoreException {
      project.restoreClassAndOpen();
      editor = project.getOpenedEditor();
   }
   
   @AfterClass
   public static void closeEditor() {
      editor.close();
   }

   @Test
   public void testOpenProposalsAfterNewAssignable() {
      goToTestOffset(1);
      final List<String> proposals = editor.getAutoCompleteProposals("");
      assertEquals(
            "Proposals after new keyword not correct",
            appendStoreRefKeywords("intermediateVector", "intermediateVectors",
                  "results", "temp", "vectors1", "vectors2"), proposals);
   }

   @Test
   public void testOpenProposalsWithToplevelPrefix() {
      goToTestOffset(2);
      final List<String> proposals = editor.getAutoCompleteProposals("");
      assertEquals("Proposals after toplevel prefix is wrong",
            Arrays.asList("vectors1", "vectors2"), proposals);
   }

   @Test
   public void testOpenProposalsFieldAccess() {
      goToTestOffset(3);
      final List<String> proposals = editor.getAutoCompleteProposals("");
      assertEquals("Field access proposals is wrong",
            Arrays.asList("*", "moreTemps", "temp1", "temp2", "temp3"),
            proposals);
      editor.autoCompleteProposal("", "moreTemps");
      editor.typeText(".");
      this.checkConsProposals();
   }

   private void checkVector2Proposals() {
      final List<String> nextProposals = editor.getAutoCompleteProposals("");
      assertEquals("Members for class Vector2 are wrong",
            Arrays.asList("*", "x", "y"), nextProposals);
   }

   private void checkConsProposals() {
      final List<String> nextProposals = editor.getAutoCompleteProposals("");
      assertEquals("Members for classes Cons are wrong",
            Arrays.asList("*", "elem", "id", "next"), nextProposals);
   }

   @Test
   public void testOpenProposalsWithParameter() {
      goToTestOffset(4);
      List<String> proposals = editor.getAutoCompleteProposals("");
      proposals = editor.getAutoCompleteProposals("");
      assertEquals(
            "Proposals with parameters not correct",
            appendStoreRefKeywords("factor", "intermediateVector",
                  "intermediateVectors", "newVector", "results", "temp",
                  "vectors1", "vectors2"), proposals);
      editor.autoCompleteProposal("", "newVector");
      editor.typeText(".");
      this.checkVector2Proposals();
   }

   @Test
   public void testGenericsCompletion() {
      goToTestOffset(5);
      this.checkConsProposals();
      editor.autoCompleteProposal("", "elem");
      editor.typeText(".");
      this.checkVector2Proposals();
   }

   @Test
   public void testNoStarAfterPrimitiveType() {
      goToTestOffset(6);
      final List<String> nextProposals = editor.getAutoCompleteProposals("");
      assertEquals("There should be no proposal after primitive type",
            Arrays.asList("No Default Proposals"), nextProposals);
   }

   @Test
   public void testStarAfterReferenceType() {
      goToTestOffset(7);
      final Position pos = editor.cursorPosition();
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      try {
         SWTBotPreferences.TIMEOUT = 1000; // Set short timeout as information hover might not be shown
         editor.autoCompleteProposal("", "");
         fail("Auto Completion list opened.");
      }
      catch (TimeoutException e) {
         // Nothing to do as auto completion is performed without opening the selection list.
      }
      finally {
         // Restore timeout
         SWTBotPreferences.TIMEOUT = originalTimeout;
      }
      // Only one proposal, is inserted by default
      assertEquals("Wrong proposals after reference type with no field", 
                   "*",
                   editor.getTextOnLine(pos.line).subSequence(pos.column, pos.column + 1));
   }

   @Test
   public void testNoStoreRefProposalsAfterSemicolon() {
      goToTestOffset(8);
      final List<String> nextProposals = editor.getAutoCompleteProposals("");
      // No Store Ref Keyword
      for (final String storeRefKeyword : appendStoreRefKeywords("")) {
         assertTrue("Proposal after semicolon contained storeRefKetword",
               !nextProposals.contains(storeRefKeyword));
      }
      // but Top Level keywords
      assertTrue("Proposals after semicolon contained no toplevel keyword",
            nextProposals.contains("assignable"));
   }

   @Test
   public void testProposalsAfterDotWithoutSemicolon() {
      goToTestOffset(9);
      this.checkConsProposals();
   }

   @Test
   public void testFinalProposals() {
      goToTestOffset(10);
      final List<String> proposals = editor.getAutoCompleteProposals("");
      assertEquals(
            "Proposed final variables for assignable",
            appendStoreRefKeywords("intermediateVector", "intermediateVectors",
                  "results", "temp", "vectors1", "vectors2"), proposals);
      goToTestOffset(11);
      final List<String> nextProposals = editor.getAutoCompleteProposals("");
      assertEquals(
            "Not proposed final variables for accessible",
            appendStoreRefKeywords("intermediateVector", "intermediateVectors",
                  "results", "temp", "vectors1", "vectors2", "doSomething",
                  "finalTemp", "secret"), nextProposals);
   }

   private static List<String> appendStoreRefKeywords(final String... others) {
      final List<String> storeRefKeywords = new ArrayList<String>();
      for (final IKeyword keyword : JMLProfileHelper.filterKeywords(
            JMLEditingUITestUtils.findReferenceProfile(), StoreRefKeywordSort.INSTANCE)) {
         storeRefKeywords.addAll(keyword.getKeywords());
      }
      storeRefKeywords.addAll(Arrays.asList(others));
      Collections.sort(storeRefKeywords);
      return storeRefKeywords;
   }

   private static void goToTestOffset(final int num) {
      editor.navigateTo(JMLEditingUITestUtils.getLineAndColumn(
            testPositions.get(num - 1), editor));
   }

}
