package org.key_project.jmlediting.ui.test.completion;

import static org.junit.Assert.assertEquals;

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
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.IStoreRefKeyword;
import org.key_project.jmlediting.ui.test.UITestUtils;
import org.key_project.jmlediting.ui.test.UITestUtils.TestProject;
import org.key_project.jmlediting.ui.test.UITestUtils.TestProject.SaveGuarantee;

public class StoreRefKeywordProposalsTest {

   private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static TestProject project;
   private static SWTBotEclipseEditor editor;
   private static List<Integer> testPositions;

   @BeforeClass
   public static void createProject() throws CoreException,
         InterruptedException, IOException {
      project = UITestUtils.createProjectWithFile(bot,
            "StoreRefKeywordProposals", StoreRefKeywordProposalsTest.class
                  .getPackage().getName(), "VectorTest",
            "data/template/storerefproposals/", SaveGuarantee.NO_SAVE);
      JMLPreferencesHelper.setProjectJMLProfile(project.getProject()
            .getProject(), UITestUtils.findReferenceProfile());
      project.restoreClassAndOpen();
      // Preprocess file
      final IFile classFile = project
            .getProject()
            .getProject()
            .getFile(
                  "src/" + project.getPackageName().replace('.', '/') + "/"
                        + project.getClassName() + ".java");
      final BufferedReader reader = new BufferedReader(new InputStreamReader(
            classFile.getContents()));
      String text = "";
      String temp;
      while ((temp = reader.readLine()) != null) {
         text += "\n" + temp;
      }

      testPositions = new ArrayList<Integer>();
      int i = 1;
      int offset;

      while ((offset = text.indexOf(getMarker(i))) != -1) {
         text = text.substring(0, offset)
               + text.substring(offset + getMarker(i).length(), text.length());
         testPositions.add(offset);
         i++;
      }

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
            Arrays.asList("*", "temp1", "temp2", "temp3", "moreTemps"),
            proposals);
      editor.autoCompleteProposal("m", "moreTemps");
      editor.insertText(".");
      final List<String> nextProposals = editor.getAutoCompleteProposals("");
      assertEquals("Field access second level is wrong",
            Arrays.asList("*", "elem", "next"), nextProposals);
   }

   private static List<String> appendStoreRefKeywords(final String... others) {
      final List<String> storeRefKeywords = new ArrayList<String>();
      for (final IStoreRefKeyword keyword : JMLProfileHelper.filterKeywords(
            UITestUtils.findReferenceProfile(), IStoreRefKeyword.class)) {
         storeRefKeywords.addAll(keyword.getKeywords());
      }
      Collections.sort(storeRefKeywords);
      storeRefKeywords.addAll(Arrays.asList(others));
      return storeRefKeywords;
   }

   private static void goToTestOffset(final int num) {
      editor.navigateTo(UITestUtils.getLineAndColumn(
            testPositions.get(num - 1), editor));
   }

}
