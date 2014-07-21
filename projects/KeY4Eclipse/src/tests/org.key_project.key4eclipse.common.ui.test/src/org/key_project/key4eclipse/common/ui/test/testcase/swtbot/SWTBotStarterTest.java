/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.key4eclipse.common.ui.test.testcase.swtbot;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotButton;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotCheckBox;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotCombo;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotLink;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotList;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotStyledText;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTabItem;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotText;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IViewPart;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.preference.page.StarterPreferencePage;
import org.key_project.key4eclipse.common.ui.starter.IFileStarter;
import org.key_project.key4eclipse.common.ui.starter.IGlobalStarter;
import org.key_project.key4eclipse.common.ui.starter.IMethodStarter;
import org.key_project.key4eclipse.common.ui.starter.IProjectStarter;
import org.key_project.key4eclipse.common.ui.test.Activator;
import org.key_project.key4eclipse.common.ui.test.starter.FirstLoggingFileStarter;
import org.key_project.key4eclipse.common.ui.test.starter.FirstLoggingGlobalStarter;
import org.key_project.key4eclipse.common.ui.test.starter.FirstLoggingMethodStarter;
import org.key_project.key4eclipse.common.ui.test.starter.FirstLoggingProjectStarter;
import org.key_project.key4eclipse.common.ui.test.starter.ITestedStarter;
import org.key_project.key4eclipse.common.ui.test.starter.SecondLoggingFileStarter;
import org.key_project.key4eclipse.common.ui.test.starter.SecondLoggingGlobalStarter;
import org.key_project.key4eclipse.common.ui.test.starter.SecondLoggingMethodStarter;
import org.key_project.key4eclipse.common.ui.test.starter.SecondLoggingProjectStarter;
import org.key_project.key4eclipse.common.ui.util.StarterDescription;
import org.key_project.key4eclipse.common.ui.util.StarterPreferenceUtil;
import org.key_project.key4eclipse.common.ui.util.StarterUtil;
import org.key_project.key4eclipse.common.ui.wizard.StarterWizard;
import org.key_project.key4eclipse.common.ui.wizard.page.StarterWizardPage;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.collection.ImmutableList;

/**
 * SWTBot tests for {@link StarterUtil}, {@link StarterWizard},
 * {@link StarterWizardPage}, {@link StarterPreferenceUtil},
 * {@link StarterPreferencePage} and the UI integration.
 * @author Martin Hentschel
 */
public class SWTBotStarterTest extends AbstractSetupTestCase {
   /**
    * Tests {@link StarterUtil#openProjectStarter(org.eclipse.swt.widgets.Shell, IProject)}
    * starter via context menu in the navigator.
    */
   @SuppressWarnings("deprecation")
   @Test
   public void testOpenProjectStarter_Navigator() throws Exception {
      doProjectStarterTest("SWTBotStarterTest_testOpenProjectStarter_Navigator", 
                           IPageLayout.ID_RES_NAV);
   }
   
   /**
    * Tests {@link StarterUtil#openProjectStarter(org.eclipse.swt.widgets.Shell, IProject)}
    * starter via context menu in the package explorer.
    */
   @Test
   public void testOpenProjectStarter_PackageExplorer() throws Exception {
      doProjectStarterTest("SWTBotStarterTest_testOpenProjectStarter_PackageExplorer", 
                           JavaUI.ID_PACKAGES);
   }
   
   /**
    * Tests {@link StarterUtil#openProjectStarter(org.eclipse.swt.widgets.Shell, IProject)}
    * starter via context menu in the project explorer.
    */
   @Test
   public void testOpenProjectStarter_ProjectExplorer() throws Exception {
      doProjectStarterTest("SWTBotStarterTest_testOpenProjectStarter_ProjectExplorer",
                           IPageLayout.ID_PROJECT_EXPLORER);
   }
   
   /**
    * Executes the test steps to test the {@link IProjectStarter} API.
    * @param projectName The project name.
    * @param fileName The file name.
    * @param viewId The ID of the view to select file in.
    * @throws Exception Occurred Exception.
    */
   protected void doProjectStarterTest(String projectName,
                                       final String viewId) throws Exception {
      // Close welcome view
      TestUtilsUtil.closeWelcomeView();
      // Create test project
      final IJavaProject project = TestUtilsUtil.createJavaProject(projectName);
      // Open view
      IViewPart alreadyOpenedView = TestUtilsUtil.findView(viewId);
      if (alreadyOpenedView == null) {
         TestUtilsUtil.openView(viewId);
      }
      try {
         // Do test
         ITestHelper<FirstLoggingProjectStarter, SecondLoggingProjectStarter> helper = new AbstractProjectTestHelper() {
            @Override
            public void openStarter(SWTWorkbenchBot bot) {
               // Select file in view
               SWTBotView view = bot.viewById(viewId);
               SWTBotTree tree = view.bot().tree();
               TestUtilsUtil.selectInTree(tree, project.getProject().getName());
               // Start proof via context menu
               TestUtilsUtil.clickContextMenu(tree, "Load Project");
            }

            @Override
            public void openStarterDirectly() throws Exception {
               StarterUtil.openProjectStarter(null, project.getProject());
            }
            
            @Override
            public void assertStarterAfterFinish(FirstLoggingProjectStarter firstStarter,
                                                 SecondLoggingProjectStarter secondStarter,
                                                 boolean firstStarterSelected) {
               ImmutableList<IProject> firstLog = firstStarter.getAndResetLog(); 
               ImmutableList<IProject> secondLog = secondStarter.getAndResetLog(); 
               if (firstStarterSelected) {
                  assertEquals(1, firstLog.size());
                  assertEquals(project.getProject(), firstLog.head());
                  assertEquals(0, secondLog.size());
               }
               else {
                  assertEquals(0, firstLog.size());
                  assertEquals(1, secondLog.size());
                  assertEquals(project.getProject(), secondLog.head());
               }
            }
         };
         ImmutableList<StarterDescription<IProjectStarter>> starters = StarterUtil.getProjectStarters();
         StarterDescription<IProjectStarter> firstSD = StarterUtil.searchStarter(starters, FirstLoggingProjectStarter.ID);
         StarterDescription<IProjectStarter> secondSD = StarterUtil.searchStarter(starters, SecondLoggingProjectStarter.ID);
         assertTrue(firstSD.getInstance() instanceof FirstLoggingProjectStarter);
         assertTrue(secondSD.getInstance() instanceof SecondLoggingProjectStarter);
         doStarterTest(helper, 
                       "Load Project", 
                       "Load Project",
                       (FirstLoggingProjectStarter)firstSD.getInstance(),
                       (SecondLoggingProjectStarter)secondSD.getInstance());
      }
      finally {
         if (alreadyOpenedView == null) {
            TestUtilsUtil.closeView(viewId);
         }
      }
   }
   
   /**
    * Tests {@link StarterUtil#openFileStarter(org.eclipse.swt.widgets.Shell, IFile)}
    * starter via context menu in the navigator.
    */
   @SuppressWarnings("deprecation")
   @Test
   public void testOpenFileStarter_Navigator() throws Exception {
      doFileStarterTest("SWTBotStarterTest_testOpenFileStarter_Navigator", 
                        "Test." + KeYUtil.PROOF_FILE_EXTENSION,
                        IPageLayout.ID_RES_NAV);
   }
   
   /**
    * Tests {@link StarterUtil#openFileStarter(org.eclipse.swt.widgets.Shell, IFile)}
    * starter via context menu in the package explorer.
    */
   @Test
   public void testOpenFileStarter_PackageExplorer() throws Exception {
      doFileStarterTest("SWTBotStarterTest_testOpenFileStarter_PackageExplorer", 
                        "Test." + KeYUtil.KEY_FILE_EXTENSION,
                        JavaUI.ID_PACKAGES);
   }
   
   /**
    * Tests {@link StarterUtil#openFileStarter(org.eclipse.swt.widgets.Shell, IFile)}
    * starter via context menu in the project explorer.
    */
   @Test
   public void testOpenFileStarter_ProjectExplorer() throws Exception {
      doFileStarterTest("SWTBotStarterTest_testOpenFileStarter_ProjectExplorer", 
                        "Test." + KeYUtil.PROOF_FILE_EXTENSION,
                        IPageLayout.ID_PROJECT_EXPLORER);
   }
   
   /**
    * Executes the test steps to test the {@link IFileStarter} API.
    * @param projectName The project name.
    * @param fileName The file name.
    * @param viewId The ID of the view to select file in.
    * @throws Exception Occurred Exception.
    */
   protected void doFileStarterTest(String projectName, 
                                    String fileName, 
                                    final String viewId) throws Exception {
      // Close welcome view
      TestUtilsUtil.closeWelcomeView();
      // Create test project
      final IProject project = TestUtilsUtil.createProject(projectName);
      final IFile file = TestUtilsUtil.createFile(project, fileName, "Hello World!");
      // Open view
      IViewPart alreadyOpenedView = TestUtilsUtil.findView(viewId);
      if (alreadyOpenedView == null) {
         TestUtilsUtil.openView(viewId);
      }
      try {
         // Do test
         ITestHelper<FirstLoggingFileStarter, SecondLoggingFileStarter> helper = new AbstractFileTestHelper() {
            @Override
            public void openStarter(SWTWorkbenchBot bot) {
               // Select file in view
               SWTBotView view = bot.viewById(viewId);
               SWTBotTree tree = view.bot().tree();
               TestUtilsUtil.selectInTree(tree, project.getName(), file.getName());
               // Start proof via context menu
               TestUtilsUtil.clickContextMenu(tree, "Load File");
            }

            @Override
            public void openStarterDirectly() throws Exception {
               StarterUtil.openFileStarter(null, file);
            }
            
            @Override
            public void assertStarterAfterFinish(FirstLoggingFileStarter firstStarter,
                                                 SecondLoggingFileStarter secondStarter,
                                                 boolean firstStarterSelected) {
               ImmutableList<IFile> firstLog = firstStarter.getAndResetLog(); 
               ImmutableList<IFile> secondLog = secondStarter.getAndResetLog(); 
               if (firstStarterSelected) {
                  assertEquals(1, firstLog.size());
                  assertEquals(file, firstLog.head());
                  assertEquals(0, secondLog.size());
               }
               else {
                  assertEquals(0, firstLog.size());
                  assertEquals(1, secondLog.size());
                  assertEquals(file, secondLog.head());
               }
            }
         };
         ImmutableList<StarterDescription<IFileStarter>> starters = StarterUtil.getFileStarters();
         StarterDescription<IFileStarter> firstSD = StarterUtil.searchStarter(starters, FirstLoggingFileStarter.ID);
         StarterDescription<IFileStarter> secondSD = StarterUtil.searchStarter(starters, SecondLoggingFileStarter.ID);
         assertTrue(firstSD.getInstance() instanceof FirstLoggingFileStarter);
         assertTrue(secondSD.getInstance() instanceof SecondLoggingFileStarter);
         doStarterTest(helper, 
                       "Load File", 
                       "Load File",
                       (FirstLoggingFileStarter)firstSD.getInstance(),
                       (SecondLoggingFileStarter)secondSD.getInstance());
      }
      finally {
         if (alreadyOpenedView == null) {
            TestUtilsUtil.closeView(viewId);
         }
      }
   }
   
   /**
    * Tests {@link StarterUtil#openMethodStarter(org.eclipse.swt.widgets.Shell, org.eclipse.jdt.core.IMethod)}
    * starter via context menu in the project explorer.
    */
   @Test
   public void testOpenMethodStarter_ProjectExplorer() throws Exception {
      // Close welcome view
      TestUtilsUtil.closeWelcomeView();
      // Create test project
      final IJavaProject project = TestUtilsUtil.createJavaProject("SWTBotStarterTest_testOpenMethodStarter_ProjectExplorer");
      final IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/paycard", src);
      TestUtilsUtil.waitForBuild();
      // Open PayCard.java
      final IMethod method = TestUtilsUtil.getJdtMethod(project, "PayCard", "charge", "I");
      assertNotNull(method);
      // Do test
      ITestHelper<FirstLoggingMethodStarter, SecondLoggingMethodStarter> helper = new AbstractMethodTestHelper() {
         @Override
         public void openStarter(SWTWorkbenchBot bot) {
            // Select method "charge(int) : boolean" in project explorer
            SWTBotView projectView = TestUtilsUtil.getProjectExplorer(bot);
            SWTBotTree projectTree = projectView.bot().tree();
            TestUtilsUtil.selectInTree(projectTree, project.getProject().getName(), src.getName(), "(default package)", "PayCard.java", "PayCard", "charge(int) : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(projectTree, "Start Proof");
         }

         @Override
         public void openStarterDirectly() throws Exception {
            StarterUtil.openMethodStarter(null, method);
         }
         
         @Override
         public void assertStarterAfterFinish(FirstLoggingMethodStarter firstStarter,
                                              SecondLoggingMethodStarter secondStarter,
                                              boolean firstStarterSelected) {
            ImmutableList<IMethod> firstLog = firstStarter.getAndResetLog(); 
            ImmutableList<IMethod> secondLog = secondStarter.getAndResetLog(); 
            if (firstStarterSelected) {
               assertEquals(1, firstLog.size());
               assertEquals(method, firstLog.head());
               assertEquals(0, secondLog.size());
            }
            else {
               assertEquals(0, firstLog.size());
               assertEquals(1, secondLog.size());
               assertEquals(method, secondLog.head());
            }
         }
      };
      doMethodStarterTest(helper);
   }
   
   /**
    * Tests {@link StarterUtil#openMethodStarter(org.eclipse.swt.widgets.Shell, org.eclipse.jdt.core.IMethod)}
    * starter via context menu in the outline view.
    */
   @Test
   public void testOpenMethodStarter_OutlineView() throws Exception {
      // Close welcome view
      TestUtilsUtil.closeWelcomeView();
      // Create test project
      IJavaProject project = TestUtilsUtil.createJavaProject("SWTBotStarterTest_testOpenMethodStarter_OutlineView");
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/paycard", src);
      TestUtilsUtil.waitForBuild();
      // Open PayCard.java
      final IEditorPart editorPart = TestUtilsUtil.openEditor(src.getFile("PayCard.java"));
      assertNotNull(editorPart);
      final IMethod method = TestUtilsUtil.getJdtMethod(project, "PayCard", "charge", "I");
      assertNotNull(method);
      try {
         // Do test
         ITestHelper<FirstLoggingMethodStarter, SecondLoggingMethodStarter> helper = new AbstractMethodTestHelper() {
            @Override
            public void openStarter(SWTWorkbenchBot bot) {
               // Select method "charge(int) : boolean" in outline view
               SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
               SWTBotTree outlineTree = outlineView.bot().tree();
               TestUtilsUtil.selectInTree(outlineTree, "PayCard", "charge(int) : boolean");
               // Start proof via context menu
               TestUtilsUtil.clickContextMenu(outlineTree, "Start Proof");
            }

            @Override
            public void openStarterDirectly() throws Exception {
               StarterUtil.openMethodStarter(null, method);
            }
            
            @Override
            public void assertStarterAfterFinish(FirstLoggingMethodStarter firstStarter,
                                                 SecondLoggingMethodStarter secondStarter,
                                                 boolean firstStarterSelected) {
               ImmutableList<IMethod> firstLog = firstStarter.getAndResetLog(); 
               ImmutableList<IMethod> secondLog = secondStarter.getAndResetLog(); 
               if (firstStarterSelected) {
                  assertEquals(1, firstLog.size());
                  assertEquals(method, firstLog.head());
                  assertEquals(0, secondLog.size());
               }
               else {
                  assertEquals(0, firstLog.size());
                  assertEquals(1, secondLog.size());
                  assertEquals(method, secondLog.head());
               }
            }
         };
         doMethodStarterTest(helper);
      }
      finally {
         TestUtilsUtil.closeEditor(editorPart, false);
      }
   }
   
   /**
    * Tests {@link StarterUtil#openMethodStarter(org.eclipse.swt.widgets.Shell, org.eclipse.jdt.core.IMethod)}
    * starter via context menu in an editor.
    */
   @Test
   public void testOpenMethodStarter_Editor() throws Exception {
      // Close welcome view
      TestUtilsUtil.closeWelcomeView();
      // Create test project
      IJavaProject project = TestUtilsUtil.createJavaProject("SWTBotStarterTest_testOpenMethodStarter_Editor");
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/paycard", src);
      TestUtilsUtil.waitForBuild();
      // Open PayCard.java
      final IEditorPart editorPart = TestUtilsUtil.openEditor(src.getFile("PayCard.java"));
      assertNotNull(editorPart);
      final IMethod method = TestUtilsUtil.getJdtMethod(project, "PayCard", "charge", "I");
      assertNotNull(method);
      try {
         // Do test
         ITestHelper<FirstLoggingMethodStarter, SecondLoggingMethodStarter> helper = new AbstractMethodTestHelper() {
            @Override
            public void openStarter(SWTWorkbenchBot bot) {
               // Set focus to outline view because otherwise the context menu of the editor does not contain the "Start Proof" menu item
               SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
               outlineView.setFocus();
               // Select method "charge(int) : boolean" in text editor
               SWTBotEditor editor = bot.editorByTitle(editorPart.getTitle());
               SWTBotStyledText styledText = editor.bot().styledText();
               styledText.selectRange(54, 18, 6);
               // Start proof via context menu
               TestUtilsUtil.clickContextMenu(styledText, "Start Proof");
            }

            @Override
            public void openStarterDirectly() throws Exception {
               StarterUtil.openMethodStarter(null, method);
            }
            
            @Override
            public void assertStarterAfterFinish(FirstLoggingMethodStarter firstStarter,
                                                 SecondLoggingMethodStarter secondStarter,
                                                 boolean firstStarterSelected) {
               ImmutableList<IMethod> firstLog = firstStarter.getAndResetLog(); 
               ImmutableList<IMethod> secondLog = secondStarter.getAndResetLog(); 
               if (firstStarterSelected) {
                  assertEquals(1, firstLog.size());
                  assertEquals(method, firstLog.head());
                  assertEquals(0, secondLog.size());
               }
               else {
                  assertEquals(0, firstLog.size());
                  assertEquals(1, secondLog.size());
                  assertEquals(method, secondLog.head());
               }
            }
         };
         doMethodStarterTest(helper);
      }
      finally {
         TestUtilsUtil.closeEditor(editorPart, false);
      }
   }
   
   /**
    * Executes the test steps to test the {@link IMethodStarter} API.
    * @param helper The {@link ITestHelper} to use.
    * @throws Exception Occurred Exception.
    */
   protected void doMethodStarterTest(ITestHelper<FirstLoggingMethodStarter, SecondLoggingMethodStarter> helper) throws Exception {
      ImmutableList<StarterDescription<IMethodStarter>> starters = StarterUtil.getMethodStarters();
      StarterDescription<IMethodStarter> firstSD = StarterUtil.searchStarter(starters, FirstLoggingMethodStarter.ID);
      StarterDescription<IMethodStarter> secondSD = StarterUtil.searchStarter(starters, SecondLoggingMethodStarter.ID);
      assertTrue(firstSD.getInstance() instanceof FirstLoggingMethodStarter);
      assertTrue(secondSD.getInstance() instanceof SecondLoggingMethodStarter);
      doStarterTest(helper, 
                    "Start Proof", 
                    "Start Proof",
                    (FirstLoggingMethodStarter)firstSD.getInstance(),
                    (SecondLoggingMethodStarter)secondSD.getInstance());
   }
   
   /**
    * Tests {@link StarterUtil#openGlobalStarter(org.eclipse.swt.widgets.Shell)}
    * starter via global tool bar.
    */
   @Test
   public void testOpenGlobalStarter_ToolBar() throws Exception {
      ITestHelper<FirstLoggingGlobalStarter, SecondLoggingGlobalStarter> helper = new AbstractGlobalTestHelper() {
         @Override
         public void openStarter(SWTWorkbenchBot bot) {
            bot.toolbarButtonWithTooltip("Open an application without loading any specific content.").click();
         }
      };
      doGlobalStarterTest(helper);
   }

   /**
    * Tests {@link StarterUtil#openGlobalStarter(org.eclipse.swt.widgets.Shell)}
    * starter via main menu.
    */
   @Test
   public void testOpenGlobalStarter_MainMenu() throws Exception {
      ITestHelper<FirstLoggingGlobalStarter, SecondLoggingGlobalStarter> helper = new AbstractGlobalTestHelper() {
         @Override
         public void openStarter(SWTWorkbenchBot bot) {
            TestUtilsUtil.menuClick(bot, "KeY", "Open Application");
         }
      };
      doGlobalStarterTest(helper);
   }
   
   /**
    * Executes the test steps to test the {@link IGlobalStarter} API.
    * @param helper The {@link ITestHelper} to use.
    * @throws Exception Occurred Exception.
    */
   protected void doGlobalStarterTest(ITestHelper<FirstLoggingGlobalStarter, SecondLoggingGlobalStarter> helper) throws Exception {
      ImmutableList<StarterDescription<IGlobalStarter>> starters = StarterUtil.getGlobalStarters();
      StarterDescription<IGlobalStarter> firstSD = StarterUtil.searchStarter(starters, FirstLoggingGlobalStarter.ID);
      StarterDescription<IGlobalStarter> secondSD = StarterUtil.searchStarter(starters, SecondLoggingGlobalStarter.ID);
      assertTrue(firstSD.getInstance() instanceof FirstLoggingGlobalStarter);
      assertTrue(secondSD.getInstance() instanceof SecondLoggingGlobalStarter);
      doStarterTest(helper, 
                    "Open Application", 
                    "Application",
                    (FirstLoggingGlobalStarter)firstSD.getInstance(),
                    (SecondLoggingGlobalStarter)secondSD.getInstance());
   }

   /**
    * Executes the test steps which tests the whole functionality of the starter API.
    * @param helper The {@link ITestHelper} to use.
    * @param wizardTitle The expected title of a {@link StarterWizard}.
    * @param preferenceTabName The expected tab name in the {@link StarterWizardPage}.
    * @param firstStarter The first starter to use during test.
    * @param secondStarter The second starter to use during test.
    * @throws Exception Occurred Exception.
    */
   protected <F extends ITestedStarter, S extends ITestedStarter> void doStarterTest(ITestHelper<F, S> helper,
                                                                                     String wizardTitle,
                                                                                     String preferenceTabName,
                                                                                     F firstStarter,
                                                                                     S secondStarter) throws Exception {
      assertNotNull(helper);
      boolean originalDisabled = helper.isDisabled();
      boolean originalDontAsk = helper.isDontAsk();
      String origianlId = helper.getSelectedId();
      SWTBotShell wizardShell = null;
      try {
         // Close welcome perspective
         SWTWorkbenchBot bot = new SWTWorkbenchBot();
         TestUtilsUtil.closeWelcomeView(bot);
         // Set default values
         helper.setDisabled(false);
         helper.setDontAsk(false);
         helper.setSelectedId(firstStarter.getId());
         assertPreferences(helper, firstStarter, false, false);
         // Test cancel
         helper.openStarter(bot);
         wizardShell = bot.shell(wizardTitle);
         assertWizard(wizardShell, firstStarter, false, false);
         cancelWizard(wizardShell);
         helper.assertStarterAfterCancel(firstStarter, secondStarter);
         assertPreferences(helper, firstStarter, false, false);
         // Test finish
         helper.openStarter(bot);
         wizardShell = bot.shell(wizardTitle);
         assertWizard(wizardShell, firstStarter, false, false);
         finishWizard(wizardShell);
         helper.assertStarterAfterFinish(firstStarter, secondStarter, true);
         assertPreferences(helper, firstStarter, false, false);
         // Test cancel second starter
         helper.openStarter(bot);
         wizardShell = bot.shell(wizardTitle);
         assertWizard(wizardShell, firstStarter, false, false);
         setSettingsInWizard(wizardShell, secondStarter, false, false);
         cancelWizard(wizardShell);
         helper.assertStarterAfterCancel(firstStarter, secondStarter);
         assertPreferences(helper, firstStarter, false, false);
         // Test finish second starter
         helper.openStarter(bot);
         wizardShell = bot.shell(wizardTitle);
         assertWizard(wizardShell, firstStarter, false, false);
         setSettingsInWizard(wizardShell, secondStarter, false, false);
         finishWizard(wizardShell);
         helper.assertStarterAfterFinish(firstStarter, secondStarter, false);
         assertPreferences(helper, secondStarter, false, false);
         // Test cancel first starter with do not ask again
         helper.openStarter(bot);
         wizardShell = bot.shell(wizardTitle);
         assertWizard(wizardShell, secondStarter, false, false);
         setSettingsInWizard(wizardShell, firstStarter, true, false);
         cancelWizard(wizardShell);
         helper.assertStarterAfterCancel(firstStarter, secondStarter);
         assertPreferences(helper, secondStarter, false, false);
         // Test finish first starter with do not ask again
         helper.openStarter(bot);
         wizardShell = bot.shell(wizardTitle);
         assertWizard(wizardShell, secondStarter, false, false);
         setSettingsInWizard(wizardShell, firstStarter, true, false);
         finishWizard(wizardShell);
         helper.assertStarterAfterFinish(firstStarter, secondStarter, true);
         assertPreferences(helper, firstStarter, true, false);
         // Test first starter without wizard
         helper.openStarter(bot);
         helper.assertStarterAfterFinish(firstStarter, secondStarter, true);
         assertPreferences(helper, firstStarter, true, false);
         // Disable do not ask
         helper.setDontAsk(false);
         assertPreferences(helper, firstStarter, false, false);
         // Test cancel second starter with disabled
         helper.openStarter(bot);
         wizardShell = bot.shell(wizardTitle);
         assertWizard(wizardShell, firstStarter, false, false);
         setSettingsInWizard(wizardShell, secondStarter, false, true);
         cancelWizard(wizardShell);
         helper.assertStarterAfterCancel(firstStarter, secondStarter);
         assertPreferences(helper, firstStarter, false, false);
         // Test finish second starter with disabled
         helper.openStarter(bot);
         wizardShell = bot.shell(wizardTitle);
         assertWizard(wizardShell, firstStarter, false, false);
         setSettingsInWizard(wizardShell, secondStarter, false, true);
         finishWizard(wizardShell);
         helper.assertStarterAfterCancel(firstStarter, secondStarter);
         assertPreferences(helper, firstStarter, false, true);
         // Test no starter because disabled
         helper.openStarterDirectly();
         helper.assertStarterAfterCancel(firstStarter, secondStarter);
         assertPreferences(helper, firstStarter, false, true);
         // Disable disabled flag
         helper.setDisabled(false);
         assertPreferences(helper, firstStarter, false, false);
         StarterUtil.updatePropertyTester();
         // Test opened preference page and cancel changes
         helper.openStarter(bot);
         wizardShell = bot.shell(wizardTitle);
         assertWizard(wizardShell, firstStarter, false, false);
         setSettingsInPreferences(wizardShell, preferenceTabName, firstStarter, false, false, secondStarter, true, true, false);
         assertWizard(wizardShell, firstStarter, false, false);
         cancelWizard(wizardShell);
         helper.assertStarterAfterCancel(firstStarter, secondStarter);
         assertPreferences(helper, firstStarter, false, false);
         // Test opened preference page and commit changed starter
         helper.openStarter(bot);
         wizardShell = bot.shell(wizardTitle);
         assertWizard(wizardShell, firstStarter, false, false);
         setSettingsInPreferences(wizardShell, preferenceTabName, firstStarter, false, false, secondStarter, false, false, true);
         assertWizard(wizardShell, secondStarter, false, false);
         assertPreferences(helper, secondStarter, false, false);
         finishWizard(wizardShell);
         helper.assertStarterAfterFinish(firstStarter, secondStarter, false);
         assertPreferences(helper, secondStarter, false, false);
         // Test opened preference page and commit changed do not ask
         helper.openStarter(bot);
         wizardShell = bot.shell(wizardTitle);
         assertWizard(wizardShell, secondStarter, false, false);
         setSettingsInPreferences(wizardShell, preferenceTabName, secondStarter, false, false, secondStarter, true, false, true);
         assertWizard(wizardShell, secondStarter, true, false);
         assertPreferences(helper, secondStarter, true, false);
         finishWizard(wizardShell);
         helper.assertStarterAfterFinish(firstStarter, secondStarter, false);
         assertPreferences(helper, secondStarter, true, false);
         // Disable do not ask
         helper.setDontAsk(false);
         assertPreferences(helper, secondStarter, false, false);
         StarterUtil.updatePropertyTester();
         // Test opened preference page and commit changed disabled
         helper.openStarter(bot);
         wizardShell = bot.shell(wizardTitle);
         assertWizard(wizardShell, secondStarter, false, false);
         setSettingsInPreferences(wizardShell, preferenceTabName, secondStarter, false, false, secondStarter, false, true, true);
         assertWizard(wizardShell, secondStarter, false, true);
         assertPreferences(helper, secondStarter, false, true);
         finishWizard(wizardShell);
         helper.assertStarterAfterCancel(firstStarter, secondStarter);
         assertPreferences(helper, secondStarter, false, true);
         // Disable disabled flag
         helper.setDisabled(false);
         assertPreferences(helper, secondStarter, false, false);
         StarterUtil.updatePropertyTester();
      }
      finally {
         helper.setDisabled(originalDisabled);
         helper.setDontAsk(originalDontAsk);
         helper.setSelectedId(origianlId);
         if (wizardShell != null && wizardShell.isOpen()) {
            wizardShell.close();
         }
      }
   }
   
   /**
    * Tests and sets the settings in the {@link StarterPreferencePage}.
    * @param wizardShell The shell of the {@link StarterWizard}.
    * @param preferenceTabName The expected tab name in the {@link StarterWizardPage}.
    * @param oldSelected The old selected {@link ITestedStarter}.
    * @param oldDontAsk The old do not ask value.
    * @param oldDisabled The old disabled value.
    * @param toSelect The new {@link ITestedStarter} to select.
    * @param dontAsk The new do not ask value to set.
    * @param disabled The new disabled value to set.
    * @param commitChanges {@code true} close preferences dialog via "OK", {@code false} close preference dialog via "Cancel".
    */
   protected <O extends ITestedStarter, N extends ITestedStarter> void setSettingsInPreferences(SWTBotShell wizardShell,
                                                                                                String preferenceTabName,
                                                                                                O oldSelected,
                                                                                                boolean oldDontAsk,
                                                                                                boolean oldDisabled,
                                                                                                N toSelect,
                                                                                                boolean dontAsk, 
                                                                                                boolean disabled,
                                                                                                boolean commitChanges) {
      SWTBotLink openLink = wizardShell.bot().link();
      openLink.click("Preferences");
      SWTBotShell preferencesShell = wizardShell.bot().shell("Preferences");
      try {
         // Test selected preference page
         SWTBotTree preferencesTree = preferencesShell.bot().tree();
         assertEquals(1, preferencesTree.selectionCount());
         assertEquals("Applications", preferencesTree.selection().get(0, 0));
         // Select tab
         SWTBotTabItem tabItem = preferencesShell.bot().tabItem(preferenceTabName);
         tabItem.activate();
         // Test existing values
         SWTBotCombo applicationsCombo = preferencesShell.bot().comboBox();
         assertEquals(oldSelected.getName(), applicationsCombo.getText());
         assertEquals(!oldDisabled, applicationsCombo.isEnabled());
         SWTBotText descriptionText = preferencesShell.bot().text(1);
         assertEquals(oldSelected.getDescription(), descriptionText.getText());
         assertEquals(!oldDisabled, descriptionText.isEnabled());
         SWTBotCheckBox dontAskBox = preferencesShell.bot().checkBox("Do not ask");
         assertEquals(oldDontAsk, dontAskBox.isChecked());
         assertEquals(!oldDisabled, dontAskBox.isEnabled());
         SWTBotCheckBox disabledBox = preferencesShell.bot().checkBox("Disable functionality");
         assertEquals(oldDisabled, disabledBox.isChecked());
         assertTrue(disabledBox.isEnabled());
         // Set new values
         applicationsCombo.setSelection(toSelect.getName());
         if (dontAsk) {
            dontAskBox.select();
         }
         else {
            dontAskBox.deselect();
         }
         if (disabled) {
            disabledBox.select();
         }
         else {
            disabledBox.deselect();
         }
         // Test new values
         assertEquals(toSelect.getName(), applicationsCombo.getText());
         assertEquals(!disabled, applicationsCombo.isEnabled());
         assertEquals(toSelect.getDescription(), descriptionText.getText());
         assertEquals(!disabled, descriptionText.isEnabled());
         assertEquals(dontAsk, dontAskBox.isChecked());
         assertEquals(!disabled, dontAskBox.isEnabled());
         assertEquals(disabled, disabledBox.isChecked());
         assertTrue(disabledBox.isEnabled());
         // Close preferences
         if (commitChanges) {
            preferencesShell.bot().button("OK").click();
         }
         else {
            preferencesShell.bot().button("Cancel").click();
         }
      }
      finally {
         if (preferencesShell != null && preferencesShell.isOpen()) {
            preferencesShell.close();
         }
      }
   }

   /**
    * Makes sure that the given preferences are set.
    * @param helper The {@link ITestHelper} to use.
    * @param expectedStarter The expected starter ID.
    * @param expectedDontAsk The expected do not ask value.
    * @param expectedDisabled The expected disabled value.
    */
   protected <F extends ITestedStarter, S extends ITestedStarter> void assertPreferences(ITestHelper<F, S> helper, 
                                                                                         ITestedStarter expectedStarter, 
                                                                                         boolean expectedDontAsk, 
                                                                                         boolean expectedDisabled) {
      assertNotNull(helper);
      assertNotNull(expectedStarter);
      assertEquals(expectedStarter.getId(), helper.getSelectedId());
      assertEquals(expectedDontAsk, helper.isDontAsk());
      assertEquals(expectedDisabled, helper.isDisabled());
   }
   
   /**
    * Finishes the wizard.
    * @param wizardShell The wizard to finish.
    */
   protected void finishWizard(SWTBotShell wizardShell) {
      SWTBotButton finishButton = wizardShell.bot().button("Finish");
      TestUtilsUtil.clickDirectly(finishButton);
      wizardShell.bot().waitUntil(Conditions.shellCloses(wizardShell));
   }
   
   /**
    * Cancels the wizard.
    * @param wizardShell The wizard to cancel.
    */
   protected void cancelWizard(SWTBotShell wizardShell) {
      SWTBotButton cancelButton = wizardShell.bot().button("Cancel");
      TestUtilsUtil.clickDirectly(cancelButton);
      wizardShell.bot().waitUntil(Conditions.shellCloses(wizardShell));
   }

   /**
    * Sets the settings in the given {@link StarterWizard}.
    * @param wizardShell The {@link StarterWizard} to modify.
    * @param toSelect The {@link ITestedStarter} to select.
    * @param dontAsk The do not ask value to set.
    * @param disabled The disabled value to set.
    */
   protected <E extends ITestedStarter> void setSettingsInWizard(SWTBotShell wizardShell, 
                                                                 E toSelect,
                                                                 boolean dontAsk, 
                                                                 boolean disabled) {
      SWTBotList applicationList = wizardShell.bot().list(); 
      applicationList.select(toSelect.getName());
      SWTBotCheckBox dontAskBox = wizardShell.bot().checkBox("Do not ask again");
      if (dontAsk) {
         dontAskBox.select();
      }
      else {
         dontAskBox.deselect();
      }
      SWTBotCheckBox disableBox = wizardShell.bot().checkBox("D&isable functionality");
      if (disabled) {
         disableBox.select();
      }
      else {
         disableBox.deselect();
      }
      assertWizard(wizardShell, toSelect, dontAsk, disabled);
   }
   
   /**
    * Makes sure that the expected values are shown in the given {@link StarterWizard}.
    * @param wizardShell The {@link StarterWizard} to test.
    * @param expectedSelectedStarter The expected {@link ITestedStarter}.
    * @param expectedDontAsk The expected do not ask value.
    * @param expectedDisabled The expected disabled value.
    */
   protected <E extends ITestedStarter> void assertWizard(SWTBotShell wizardShell, 
                                                          E expectedSelectedStarter,
                                                          boolean expectedDontAsk, 
                                                          boolean expectedDisabled) {
      // Assert starter
      SWTBotList applicationList = wizardShell.bot().list(); 
      String[] selectedItems = applicationList.selection();
      assertEquals(1, selectedItems.length);
      assertEquals(expectedSelectedStarter.getName(), selectedItems[0]);
      assertEquals(!expectedDisabled, applicationList.isEnabled());
      // Assert starter description
      SWTBotText descriptionText = wizardShell.bot().text();
      assertEquals(expectedSelectedStarter.getDescription(), descriptionText.getText());
      assertEquals(!expectedDisabled, descriptionText.isEnabled());
      // Assert do not ask
      SWTBotCheckBox dontAskBox = wizardShell.bot().checkBox("Do not ask again");
      assertEquals(expectedDontAsk, dontAskBox.isChecked());
      assertEquals(!expectedDisabled, dontAskBox.isEnabled());
      // Assert disabled
      SWTBotCheckBox disableBox = wizardShell.bot().checkBox("D&isable functionality");
      assertEquals(expectedDisabled, disableBox.isChecked());
      assertTrue(disableBox.isEnabled());
   }

   /**
    * Provides a basic functionality of {@link ITestHelper} which tests {@link IProjectStarter}s.
    * @author Martin Hentschel
    */
   protected static abstract class AbstractProjectTestHelper implements ITestHelper<FirstLoggingProjectStarter, SecondLoggingProjectStarter> {
      /**
       * {@inheritDoc}
       */
      @Override
      public void assertStarterAfterCancel(FirstLoggingProjectStarter firstStarter,
                                           SecondLoggingProjectStarter secondStarter) {
         ImmutableList<IProject> firstLog = firstStarter.getAndResetLog(); 
         ImmutableList<IProject> secondLog = secondStarter.getAndResetLog(); 
         assertEquals(0, firstLog.size());
         assertEquals(0, secondLog.size());
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isDisabled() {
         return StarterPreferenceUtil.isProjectStarterDisabled();
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void setDisabled(boolean disabled) {
         StarterPreferenceUtil.setProjectStarterDisabled(disabled);
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isDontAsk() {
         return StarterPreferenceUtil.isDontAskForProjectStarter();
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void setDontAsk(boolean dontAsk) {
         StarterPreferenceUtil.setDontAskForProjectStarter(dontAsk);
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public String getSelectedId() {
         return StarterPreferenceUtil.getSelectedProjectStarterID();
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void setSelectedId(String id) {
         StarterPreferenceUtil.setSelectedProjectStarterID(id);
      }
   }

   /**
    * Provides a basic functionality of {@link ITestHelper} which tests {@link IFileStarter}s.
    * @author Martin Hentschel
    */
   protected static abstract class AbstractFileTestHelper implements ITestHelper<FirstLoggingFileStarter, SecondLoggingFileStarter> {
      /**
       * {@inheritDoc}
       */
      @Override
      public void assertStarterAfterCancel(FirstLoggingFileStarter firstStarter,
                                           SecondLoggingFileStarter secondStarter) {
         ImmutableList<IFile> firstLog = firstStarter.getAndResetLog(); 
         ImmutableList<IFile> secondLog = secondStarter.getAndResetLog(); 
         assertEquals(0, firstLog.size());
         assertEquals(0, secondLog.size());
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isDisabled() {
         return StarterPreferenceUtil.isFileStarterDisabled();
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void setDisabled(boolean disabled) {
         StarterPreferenceUtil.setFileStarterDisabled(disabled);
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isDontAsk() {
         return StarterPreferenceUtil.isDontAskForFileStarter();
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void setDontAsk(boolean dontAsk) {
         StarterPreferenceUtil.setDontAskForFileStarter(dontAsk);
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public String getSelectedId() {
         return StarterPreferenceUtil.getSelectedFileStarterID();
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void setSelectedId(String id) {
         StarterPreferenceUtil.setSelectedFileStarterID(id);
      }
   }

   /**
    * Provides a basic functionality of {@link ITestHelper} which tests {@link IMethodStarter}s.
    * @author Martin Hentschel
    */
   protected static abstract class AbstractMethodTestHelper implements ITestHelper<FirstLoggingMethodStarter, SecondLoggingMethodStarter> {
      /**
       * {@inheritDoc}
       */
      @Override
      public void assertStarterAfterCancel(FirstLoggingMethodStarter firstStarter,
                                           SecondLoggingMethodStarter secondStarter) {
         ImmutableList<IMethod> firstLog = firstStarter.getAndResetLog(); 
         ImmutableList<IMethod> secondLog = secondStarter.getAndResetLog(); 
         assertEquals(0, firstLog.size());
         assertEquals(0, secondLog.size());
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isDisabled() {
         return StarterPreferenceUtil.isMethodStarterDisabled();
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void setDisabled(boolean disabled) {
         StarterPreferenceUtil.setMethodStarterDisabled(disabled);
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isDontAsk() {
         return StarterPreferenceUtil.isDontAskForMethodStarter();
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void setDontAsk(boolean dontAsk) {
         StarterPreferenceUtil.setDontAskForMethodStarter(dontAsk);
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public String getSelectedId() {
         return StarterPreferenceUtil.getSelectedMethodStarterID();
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void setSelectedId(String id) {
         StarterPreferenceUtil.setSelectedMethodStarterID(id);
      }
   }

   /**
    * Provides a basic functionality of {@link ITestHelper} which tests {@link IGlobalStarter}s.
    * @author Martin Hentschel
    */
   protected static abstract class AbstractGlobalTestHelper implements ITestHelper<FirstLoggingGlobalStarter, SecondLoggingGlobalStarter> {
      /**
       * {@inheritDoc}
       */
      @Override
      public void openStarterDirectly() throws Exception {
         StarterUtil.openGlobalStarter(null);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void assertStarterAfterCancel(FirstLoggingGlobalStarter firstStarter,
                                           SecondLoggingGlobalStarter secondStarter) {
         assertEquals(0, firstStarter.getAndResetOpenCount());
         assertEquals(0, secondStarter.getAndResetOpenCount());
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void assertStarterAfterFinish(FirstLoggingGlobalStarter firstStarter,
                                           SecondLoggingGlobalStarter secondStarter,
                                           boolean firstStarterSelected) {
         if (firstStarterSelected) {
            assertEquals(1, firstStarter.getAndResetOpenCount());
            assertEquals(0, secondStarter.getAndResetOpenCount());
         }
         else {
            assertEquals(0, firstStarter.getAndResetOpenCount());
            assertEquals(1, secondStarter.getAndResetOpenCount());
         }
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isDisabled() {
         return StarterPreferenceUtil.isGlobalStarterDisabled();
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void setDisabled(boolean disabled) {
         StarterPreferenceUtil.setGlobalStarterDisabled(disabled);
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isDontAsk() {
         return StarterPreferenceUtil.isDontAskForGlobalStarter();
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void setDontAsk(boolean dontAsk) {
         StarterPreferenceUtil.setDontAskForGlobalStarter(dontAsk);
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public String getSelectedId() {
         return StarterPreferenceUtil.getSelectedGlobalStarterID();
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void setSelectedId(String id) {
         StarterPreferenceUtil.setSelectedGlobalStarterID(id);
      }
   }
   
   /**
    * Utility class used in {@link SWTBotStarterTest#doStarterTest(ITestHelper, String, String, ITestedStarter, ITestedStarter)}
    * to perform a part of the test.
    * @author Martin Hentschel
    */
   protected static interface ITestHelper<F extends ITestedStarter, S extends ITestedStarter> {
      /**
       * Opens the starter via UI.
       * @param bot The {@link SWTWorkbenchBot} to use.
       */
      public void openStarter(SWTWorkbenchBot bot);
      
      /**
       * Opens the starter programatically via {@link StarterUtil}.
       * @throws Exception Occurred Exception
       */
      public void openStarterDirectly() throws Exception;

      /**
       * Makes sure that nothing was started.
       * @param firstStarter The first starter.
       * @param secondStarter The second starter.
       */
      public void assertStarterAfterCancel(F firstStarter, S secondStarter);
      
      /**
       * Makes sure that one starter was executed.
       * @param firstStarter The first starter.
       * @param secondStarter The second starter.
       * @param firstStarterSelected {@code true} first starter executed, {@code false} second starter executed.
       */
      public void assertStarterAfterFinish(F firstStarter, S secondStarter, boolean firstStarterSelected);
      
      /**
       * Checks if preference disabled is active.
       * @return {@code true} disabled, {@code false} enabled.
       */
      public boolean isDisabled();
      
      /**
       * Sets preference disabled.
       * @param disabled {@code true} disabled, {@code false} enabled.
       */
      public void setDisabled(boolean disabled);
      
      /**
       * Checks if preference do not ask is active.
       * @return {@code true} do not ask, {@code false} ask
       */
      public boolean isDontAsk();
      
      /**
       * Sets preference do not ask.
       * @param dontAsk {@code true} do not ask, {@code false} ask
       */
      public void setDontAsk(boolean dontAsk);
      
      /**
       * Returns the ID of the selected starter from the preferences.
       * @return The ID of the selected starter.
       */
      public String getSelectedId();
      
      /**
       * Sets the ID of the selected starter in the preferences.
       * @param id The ID of the selected starter to set.
       */
      public void setSelectedId(String id);
   }
}