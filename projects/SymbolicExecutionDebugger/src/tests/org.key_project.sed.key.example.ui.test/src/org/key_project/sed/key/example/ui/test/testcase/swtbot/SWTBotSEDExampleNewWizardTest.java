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

package org.key_project.sed.key.example.ui.test.testcase.swtbot;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotText;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.core.test.testcase.swtbot.AbstractKeYDebugTargetTestCase;
import org.key_project.sed.key.example.ui.test.Activator;
import org.key_project.sed.key.example.ui.wizard.SEDExampleNewWizard;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * SWTBot tests for {@link SEDExampleNewWizard}.
 * @author Martin Hentschel
 */
public class SWTBotSEDExampleNewWizardTest extends AbstractKeYDebugTargetTestCase {
   /**
    * Tests 'example1'.
    */
   @Test
   public void testExample1() throws Exception {
      doExampleResumeTest("SWTBotSEDExampleNewWizardTest_testExample1",
                          createMethodSelector("example1.Number", "equals", "QNumber;"),
                          false,
                          null,
                          "data/oracle/example1/Number.xml",
                          false,
                          false);
   }
   
   /**
    * Tests 'example2' without precondition.
    */
   @Test
   public void testExample2_noPrecondition() throws Exception {
      doStepIntoTest("SWTBotSEDExampleNewWizardTest_testExample2_noPrecondition",
                     createMethodSelector("example2.QuickSort", "sort"),
                     false,
                     null,
                     3,
                     "data/oracle/example2/QuickSort_NoPrecondition.xml");
   }
   
   /**
    * Tests 'example2' with precondition.
    */
   @Test
   public void testExample2_withPrecondition() throws Exception {
      doStepIntoTest("SWTBotSEDExampleNewWizardTest_testExample2_withPrecondition",
                     createMethodSelector("example2.QuickSort", "sort"),
                     false,
                     "numbers != null & numbers.length >= 1",
                     5,
                     "data/oracle/example2/QuickSort_WithPrecondition.xml");
   }
   
   /**
    * Tests 'example3'.
    */
   @Test
   public void testExample3() throws Exception {
      doExampleResumeTest("SWTBotSEDExampleNewWizardTest_testExample3",
                          createMethodSelector("example3.ArrayUtil", "indexOf", "[QObject;", "QFilter;"),
                          true,
                          "example3.ArrayUtil[example3.ArrayUtil::indexOf([Ljava.lang.Object,example3.ArrayUtil.Filter)].JML normal_behavior operation contract.0",
                          "data/oracle/example3/ArrayUtil.xml",
                          true,
                          true);
   }
   
   /**
    * Tests 'example3'.
    */
   @Test
   public void testExample4() throws Exception {
      doExampleResumeTest("SWTBotSEDExampleNewWizardTest_testExample4",
                          createMethodSelector("example4.AVLTree", "rotateLeft", "QNode;"),
                          false,
                          null,
                          "data/oracle/example4/AVLTree.xml",
                          false,
                          false);
      // TODO: Test symbolic memory configuration visualization
   }
   
   /**
    * Performs step into multiple times.
    * @param projectName The example project name.
    * @param selector The {@link IMethodSelector} to select the {@link IMethod} to debug.
    * @param useExistingContract Use existing contract? Use {@code null} to use default value.
    * @param preconditionOrExistingContract Optional precondition or the ID of the existing contract to use Use {@code null} to use default value.
    * @param numberOfStepIntos The number of step into operations to execute.
    * @param expectedModelPathInBundle The path to the oracle file.
    * @throws Exception Occurred Exception.
    */
   protected void doStepIntoTest(String projectName, 
                                 final IMethodSelector selector,
                                 final Boolean useExistingContract,
                                 final String preconditionOrExistingContract,
                                 final int numberOfStepIntos,
                                 final String expectedModelPathInBundle) throws Exception {
      IExampleTestSteps steps = new IExampleTestSteps() {
         @Override
         public void doTest(IJavaProject javaProject) throws Exception {
            IKeYDebugTargetTestExecutor executor = new AbstractKeYDebugTargetTestExecutor() {
               @Override
               public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
                  SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0); // Select thread
                  for (int i = 0; i < numberOfStepIntos; i++) {
                     stepInto(bot, item, target);
                  }
                  assertDebugTargetViaOracle(target, Activator.PLUGIN_ID, expectedModelPathInBundle, false, false, false);
               }
            };
            doKeYDebugTargetTest(javaProject, true, true, selector, useExistingContract, preconditionOrExistingContract, false, false, false, false, false, false, true, 10, executor);
         }
      };
      doExampleTest(projectName, steps);
   }
   
   /**
    * Resumes a method until it is completely symbolically executed.
    * @param projectName The example project name.
    * @param selector The {@link IMethodSelector} to select the {@link IMethod} to debug.
    * @param useExistingContract Use existing contract? Use {@code null} to use default value.
    * @param preconditionOrExistingContract Optional precondition or the ID of the existing contract to use Use {@code null} to use default value.
    * @param expectedModelPathInBundle The path to the oracle file.
    * @param useMethodContracts Use method contracts?
    * @param useLoopInvariants Use loop invariants?
    * @throws Exception Occurred Exception.
    */
   protected void doExampleResumeTest(String projectName, 
                                      final IMethodSelector selector,
                                      final Boolean useExistingContract,
                                      final String preconditionOrExistingContract,
                                      final String expectedModelPathInBundle,
                                      final boolean useMethodContracts,
                                      final boolean useLoopInvariants) throws Exception {
      IExampleTestSteps steps = new IExampleTestSteps() {
         @Override
         public void doTest(IJavaProject javaProject) throws Exception {
            IKeYDebugTargetTestExecutor executor = createResumeExecutor(false, Activator.PLUGIN_ID, expectedModelPathInBundle, false, false, false, false, false, useMethodContracts, useLoopInvariants, false, false);
            doKeYDebugTargetTest(javaProject, true, true, selector, useExistingContract, preconditionOrExistingContract, false, false, false, false, false, false, true, 10, executor);
         }
      };
      doExampleTest(projectName, steps);
   }
   
   /**
    * Tests something in the example project.
    * @param projectName The example project name.
    * @param steps The test steps to execute.
    * @throws Exception Occurred Exception.
    */
   protected void doExampleTest(String projectName,
                                IExampleTestSteps steps) throws Exception {
      IPerspectiveDescriptor originalPerspective = TestUtilsUtil.getActivePerspective();
      try {
         SWTWorkbenchBot bot = new SWTWorkbenchBot();
         // Open Java perspective
         TestUtilsUtil.openJavaPerspective();
         // Open new example wizard
         TestUtilsUtil.menuClick(bot, "File", "New", "Example...");
         SWTBotShell shell = bot.shell("New Example");
         //  Open Banking Example wizard
         TestUtilsUtil.selectInTree(shell.bot().tree(), "Symbolic Execution Debugger (SED)", "SED Examples");
         TestUtilsUtil.clickDirectly(shell.bot(), "Next >");
         // Define project name
         SWTBotText text = shell.bot().text(0);
         text.setText(projectName);
         // Finish wizard
         TestUtilsUtil.clickDirectly(shell.bot(), "Finish");
         shell.bot().waitUntil(Conditions.shellCloses(shell));
         // Test created project
         IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject(projectName);
         assertTrue(project.exists());
         assertTrue(project.isOpen());
         IJavaProject javaProject = JavaCore.create(project);
         assertNotNull(javaProject);
         assertTrue(javaProject.exists());
         // Unify line breaks
         TestUtilsUtil.unifyLineBreaks(project, "java");
         // Test opened editor
         SWTBotEditor editor = bot.activeEditor();
         assertEquals(project.getFile(new Path("Readme.txt")), editor.getReference().getEditorInput().getAdapter(IFile.class));
         editor.close();
         // Do test
         steps.doTest(javaProject);
      }
      finally {
         // Restore perspective
         TestUtilsUtil.openPerspective(originalPerspective);
      }
   }
   
   /**
    * Test steps executed by {@link SWTBotSEDExampleNewWizardTest#doExampleTest(String, IExampleTestSteps)}.
    * @author Martin Hentschel
    */
   private static interface IExampleTestSteps {
      /**
       * Executes the test steps.
       * @param javaProject The example project.
       * @throws Exception Occurred Exception.
       */
      public void doTest(IJavaProject javaProject) throws Exception;
   }
}