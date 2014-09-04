package org.key_project.key4eclipse.resources.ui.test.testcase.swtbot;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotCTabItem;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.eclipse.ui.IEditorPart;
import org.junit.Before;
import org.junit.Test;
import org.key_project.key4eclipse.resources.log.LogManager;
import org.key_project.key4eclipse.resources.log.LogRecord;
import org.key_project.key4eclipse.resources.test.testcase.junit.AbstractResourceTest;
import org.key_project.key4eclipse.resources.test.util.KeY4EclipseResourcesTestUtil;
import org.key_project.key4eclipse.resources.ui.test.Activator;
import org.key_project.key4eclipse.resources.ui.view.VerificationLogView;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * SWTBot tests for {@link VerificationLogView}.
 * @author Martin Hentschel
 */
public class SWTBotVerificationLogViewTest extends AbstractResourceTest {
   /**
    * {@inheritDoc}
    */
   @Before
   @Override
   public void setUp() throws Exception {
      super.setUp();
      // Ensure that no other KeY project is open
      IProject[] projects = ResourcesPlugin.getWorkspace().getRoot().getProjects();
      for (IProject project : projects) {
         if (KeYResourcesUtil.isKeYProject(project)) {
            project.close(null);
         }
      }
      TestUtilsUtil.waitForBuild();
   }
   
   /**
    * Ensures that new log records are shown after a build.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testBuilds() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotView view = null;
      IProject keyProject = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Open view and ensure that no content is shown.
         TestUtilsUtil.openView(VerificationLogView.VIEW_ID);
         view = bot.viewById(VerificationLogView.VIEW_ID);
         assertProjectShown(view);
         // Create first key project to show
         keyProject = KeY4EclipseResourcesTestUtil.initializeTest("SWTBotVerificationLogViewTest_testBuilds", true, true, false, 1, true, true);
         assertProjectShown(view, keyProject);
         assertEquals(1, LogManager.getInstance().countRecords(keyProject));
         assertEquals(1, view.bot().table().rowCount());
         LogRecord firstRecord = LogManager.getInstance().readRecord(keyProject, 0);
         // Perform second build
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/classWithoutMethods", keyProject.getFolder("src"));
         KeY4EclipseResourcesTestUtil.build(keyProject);
         assertProjectShown(view, keyProject);
         assertEquals(2, LogManager.getInstance().countRecords(keyProject));
         assertEquals(2, view.bot().table().rowCount());
         LogRecord secondRecord = LogManager.getInstance().readRecord(keyProject, 1);
         assertEquals(firstRecord, LogManager.getInstance().readRecord(keyProject, 0));
         assertFalse(firstRecord.equals(secondRecord));
      }
      finally {
         if (view != null) {
            view.close();
         }
         if (keyProject != null) {
            keyProject.delete(true, true, null);
            KeY4EclipseResourcesTestUtil.build(keyProject);
         }
      }
   }
   
   /**
    * Tests clear log.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testClearLog() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotView view = null;
      IProject firstKeyProject = null;
      IProject secondKeyProject = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Open view and ensure that no content is shown.
         TestUtilsUtil.openView(VerificationLogView.VIEW_ID);
         view = bot.viewById(VerificationLogView.VIEW_ID);
         assertProjectShown(view);
         // Create first key project to show
         firstKeyProject = KeY4EclipseResourcesTestUtil.initializeTest("SWTBotVerificationLogViewTest_testClearLog_key1", true, true, false, 1, true, true);
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/classWithoutMethods", firstKeyProject.getFolder("src"));
         KeY4EclipseResourcesTestUtil.build(firstKeyProject);
         KeY4EclipseResourcesTestUtil.build(firstKeyProject);
         assertProjectShown(view, firstKeyProject);
         // Create second key project to show
         secondKeyProject = KeY4EclipseResourcesTestUtil.initializeTest("SWTBotVerificationLogViewTest_testClearLog_key2", true, true, false, 1, true, true);
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/classWithoutMethods", secondKeyProject.getFolder("src"));
         KeY4EclipseResourcesTestUtil.build(secondKeyProject);
         KeY4EclipseResourcesTestUtil.build(secondKeyProject);
         assertProjectShown(view, firstKeyProject, secondKeyProject);
         // Test initial logs
         assertEquals(2, LogManager.getInstance().countRecords(firstKeyProject));
         assertEquals(2, LogManager.getInstance().countRecords(secondKeyProject));
         assertEquals(2, view.bot().table().rowCount());
         // Cancel clear log
         view.toolbarPushButton("Clear Log").click();
         view.bot().shell("Confirm clear log").bot().button("Cancel").click();
         // Test logs again
         assertEquals(2, LogManager.getInstance().countRecords(firstKeyProject));
         assertEquals(2, LogManager.getInstance().countRecords(secondKeyProject));
         assertEquals(2, view.bot().table().rowCount());
         // Commit clear log
         view.toolbarPushButton("Clear Log").click();
         view.bot().shell("Confirm clear log").bot().button("OK").click();
         // Test logs again
         assertEquals(0, LogManager.getInstance().countRecords(firstKeyProject));
         assertEquals(2, LogManager.getInstance().countRecords(secondKeyProject));
         assertEquals(0, view.bot().table().rowCount());
      }
      finally {
         if (view != null) {
            view.close();
         }
         if (firstKeyProject != null) {
            firstKeyProject.delete(true, true, null);
            KeY4EclipseResourcesTestUtil.build(firstKeyProject);
         }
         if (secondKeyProject != null) {
            secondKeyProject.delete(true, true, null);
            KeY4EclipseResourcesTestUtil.build(secondKeyProject);
         }
      }
   }
   
   /**
    * Ensures that the correct logs are shown with and without linking.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testShownContentWithAndWithoutLinking() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotView view = null;
      IProject generalProject = null;
      IProject firstKeyProject = null;
      IJavaProject javaProject = null;
      IProject secondKeyProject = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Open view and ensure that no content is shown.
         TestUtilsUtil.openView(VerificationLogView.VIEW_ID);
         view = bot.viewById(VerificationLogView.VIEW_ID);
         assertProjectShown(view);
         // Create general project not to be shown
         generalProject = TestUtilsUtil.createProject("SWTBotVerificationLogViewTest_testShownContentWithAndWithoutLinking_general");
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/classWithoutMethods", generalProject);
         KeY4EclipseResourcesTestUtil.build(generalProject);
         assertProjectShown(view);
         // Create first key project to show
         firstKeyProject = KeY4EclipseResourcesTestUtil.initializeTest("SWTBotVerificationLogViewTest_testShownContentWithAndWithoutLinking_key1", true, true, false, 1, true, true);
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/classWithoutMethods", firstKeyProject.getFolder("src"));
         KeY4EclipseResourcesTestUtil.build(firstKeyProject);
         assertProjectShown(view, firstKeyProject);
         // Create java project not to be shown
         javaProject = TestUtilsUtil.createJavaProject("SWTBotVerificationLogViewTest_testShownContentWithAndWithoutLinking_java");
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/classWithoutMethods", javaProject.getProject().getFolder("src"));
         KeY4EclipseResourcesTestUtil.build(javaProject.getProject());
         assertProjectShown(view, firstKeyProject);
         // Create second key project to show
         secondKeyProject = KeY4EclipseResourcesTestUtil.initializeTest("SWTBotVerificationLogViewTest_testShownContentWithAndWithoutLinking_key2", true, true, false, 1, true, true);
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/classWithoutMethods", secondKeyProject.getFolder("src"));
         KeY4EclipseResourcesTestUtil.build(secondKeyProject);
         assertProjectShown(view, firstKeyProject, secondKeyProject);
         // Open editors
         final IFile firstFile = firstKeyProject.getFile(new Path("src/myPackage/MyClass.java"));
         IEditorPart firstEditorPart = TestUtilsUtil.openEditor(firstFile);
         SWTBotEditor firstEditor = bot.activeEditor();
         assertSame(firstEditorPart, firstEditor.getReference().getEditor(false));
         final IFile secondFile = secondKeyProject.getFile(new Path("src/myPackage/MyClass.java"));
         IEditorPart secondEditorPart = TestUtilsUtil.openEditor(secondFile);
         SWTBotEditor secondEditor = bot.activeEditor();
         assertSame(secondEditorPart, secondEditor.getReference().getEditor(false));
         assertProjectShown(view, firstKeyProject, secondKeyProject);
         // Get project explorer
         SWTBotView projectExplorer = TestUtilsUtil.getProjectExplorer(bot);
         // Enable linking
         view.toolbarToggleButton("Link with Editor/View").click();
         // Switch between editors and project explorer with linking
         firstEditor.show();
         assertSelection(view, firstFile, firstKeyProject, secondKeyProject);
         assertProjectShown(view, firstKeyProject);
         secondEditor.show();
         assertSelection(view, secondFile, firstKeyProject, secondKeyProject);
         assertProjectShown(view, secondKeyProject);
         // Select different content in project explorer
         projectExplorer.show();
         TestUtilsUtil.selectAndReveal(firstFile);
         assertSelection(view, firstFile, firstKeyProject, secondKeyProject);
         assertProjectShown(view, firstKeyProject);
         TestUtilsUtil.selectAndReveal(secondFile);
         assertSelection(view, secondFile, firstKeyProject, secondKeyProject);
         assertProjectShown(view, secondKeyProject);
         // Disable linking
         view.toolbarToggleButton("Link with Editor/View").click();
         // Switch between editors and project explorer without linking
         projectExplorer.show();
         assertProjectShown(view, firstKeyProject, secondKeyProject);
         firstEditor.show();
         assertProjectShown(view, firstKeyProject, secondKeyProject);
         secondEditor.show();
         assertProjectShown(view, firstKeyProject, secondKeyProject);
         projectExplorer.show();
         assertProjectShown(view, firstKeyProject, secondKeyProject);
         // Select different content in project explorer
         TestUtilsUtil.selectAndReveal(firstFile);
         assertProjectShown(view, firstKeyProject, secondKeyProject);
         TestUtilsUtil.selectAndReveal(secondFile);
         assertProjectShown(view, firstKeyProject, secondKeyProject);
      }
      finally {
         bot.closeAllEditors();
         if (view != null) {
            view.close();
         }
         if (generalProject != null) {
            generalProject.delete(true, true, null);
            KeY4EclipseResourcesTestUtil.build(generalProject);
         }
         if (firstKeyProject != null) {
            firstKeyProject.delete(true, true, null);
            KeY4EclipseResourcesTestUtil.build(firstKeyProject);
         }
         if (javaProject != null) {
            javaProject.getProject().delete(true, true, null);
            KeY4EclipseResourcesTestUtil.build(javaProject.getProject());
         }
         if (secondKeyProject != null) {
            secondKeyProject.delete(true, true, null);
            KeY4EclipseResourcesTestUtil.build(secondKeyProject);
         }
      }
   }
   
   /**
    * Ensures the correct selection.
    * @param view The {@link SWTBotView} to test.
    * @param resource The expected selected {@link IResource}.
    * @param allProjects All available KeY projects.
    * @throws Exception Occurred exception.
    */
   protected void assertSelection(SWTBotView view, IResource resource, IProject... allProjects) throws Exception {
      for (IProject project : allProjects) {
         SWTBotCTabItem tabItem = view.bot().cTabItem(project.getName());
         assertEquals(project.equals(resource.getProject()), tabItem.isActive());
      }
   }

   /**
    * Ensures that the given {@link IProject}s are shown.
    * @param view The {@link SWTBotView} to test.
    * @param projects The expected shown {@link IProject}s.
    * @throws Exception Occurred exception.
    */
   protected void assertProjectShown(SWTBotView view, IProject... projects) throws Exception {
      SWTBotCTabItem activeItem = null;
      for (IProject project : projects) {
         SWTBotCTabItem tabItem = view.bot().cTabItem(project.getName());
         if (tabItem.isActive()) {
            activeItem = tabItem;
         }
         tabItem.show();
         SWTBotTable table = view.bot().table();
         assertEquals(LogManager.getInstance().countRecords(project), table.rowCount());
      }
      if (projects.length == 0) {
         assertNull(activeItem);
      }
      else {
         assertNotNull(activeItem);
         activeItem.show();
      }
   }
}
