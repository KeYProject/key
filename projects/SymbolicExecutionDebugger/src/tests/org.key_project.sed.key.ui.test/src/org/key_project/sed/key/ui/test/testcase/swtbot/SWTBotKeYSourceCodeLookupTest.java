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

package org.key_project.sed.key.ui.test.testcase.swtbot;

import java.io.File;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.core.model.ISourceLocator;
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotMenu;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.junit.Before;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.test.util.DebugTargetResumeSuspendListener;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.core.launch.KeYSourceLookupDirector;
import org.key_project.sed.key.core.launch.KeYSourceLookupParticipant;
import org.key_project.sed.key.core.test.util.TestSEDKeyCoreUtil;
import org.key_project.sed.key.ui.presentation.KeYDebugModelPresentation;
import org.key_project.sed.key.ui.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests the source code lookup implemented in {@link KeYSourceLookupParticipant} 
 * and {@link KeYSourceLookupDirector}. Also a real lookup in the UI is tested
 * which involves the {@link KeYDebugModelPresentation}.
 * @author Martin Hentschel
 */
public class SWTBotKeYSourceCodeLookupTest extends AbstractSetupTestCase {
   /**
    * {@inheritDoc}
    */
   @Before
   @Override
   public void setUp() throws Exception {
      super.setUp();
      // Close welcome view
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      TestUtilsUtil.closeWelcomeView(bot);
      // Make sure that all editors are closed
      bot.closeAllEditors();
   }
   
   /**
    * Makes sure that the correct source files are opened and that the
    * correct source code lines are selected.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testLookupMarkerInUI() throws Exception {
      // Create bot
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      // Get current settings to restore them in finally block
      IPerspectiveDescriptor defaultPerspective = TestUtilsUtil.getActivePerspective();
      SWTBotTree debugTree = null;
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      try {
         // Open symbolic debug perspective
         TestSedCoreUtil.openSymbolicDebugPerspective();
         // Create test project
         IJavaProject project = TestUtilsUtil.createJavaProject("SWTBotKeYSourceLookupParticipantTest_testLookupMarkerInUI");
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/statements", project.getProject().getFolder("src"));
         // Get method
         IMethod method = TestUtilsUtil.getJdtMethod(project, "FlatSteps", "doSomething", "I", "QString;", "Z");
         // Increase timeout
         SWTBotPreferences.TIMEOUT = SWTBotPreferences.TIMEOUT * 8;
         // Launch method
         TestSEDKeyCoreUtil.launchKeY(method, null, null, Boolean.FALSE, Boolean.FALSE, Boolean.FALSE, Boolean.FALSE, Boolean.FALSE, Boolean.FALSE, Boolean.TRUE);
         // Find the launched ILaunch in the debug view
         SWTBotView debugView = TestSedCoreUtil.getDebugView(bot);
         debugTree = debugView.bot().tree();
         ISEDDebugTarget target = TestSedCoreUtil.waitUntilDebugTreeHasDebugTarget(bot, debugTree);
         // Click on "Resume" and wait until step was executed.
         final SWTBotTreeItem item = TestUtilsUtil.selectInTree(debugTree, 0, 0); // Select first debug target
         DebugTargetResumeSuspendListener.run(bot, target, new Runnable() {
            @Override
            public void run() {
               SWTBotMenu menuItem = item.contextMenu("Resume"); 
               menuItem.click();
            }
         });
         // Test the execution tree
         TestSEDKeyCoreUtil.assertFlatStepsExample(target);
         // Make sure that no editor is opened
         assertEquals(1, bot.editors().size());
         assertEquals("FlatSteps.java", bot.activeEditor().getTitle());
         // Test statements
         assertSelectedStatement(bot, debugTree, new int[] {0, 0, 0, 1}, method, target, true);
         assertSelectedStatement(bot, debugTree, new int[] {0, 0, 0, 2}, method, target, false);
         assertSelectedStatement(bot, debugTree, new int[] {0, 0, 0, 3}, method, target, true);
      }
      finally {
         // Restore timeout
         SWTBotPreferences.TIMEOUT = originalTimeout;
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
         // Restore perspective
         TestUtilsUtil.openPerspective(defaultPerspective);
         // Make sure that all editors are closed
         bot.closeAllEditors();
      }
   }
   
   /**
    * Tests the opened editor by the debug API and the annotated line.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param debugTree The debug tree to select in.
    * @param pathToStatementInTree The path to the item to select in the debug tree.
    * @param method The tested {@link IMethod}.
    * @param target The launched {@link IDebugTarget}.
    * @param closeEditor Close opened editor?
    * @throws CoreException Occurred Exception
    * @throws BadLocationException Occurred Exception
    */
   protected void assertSelectedStatement(SWTWorkbenchBot bot, 
                                          SWTBotTree debugTree, 
                                          int[] pathToStatementInTree,
                                          IMethod method,
                                          IDebugTarget target,
                                          boolean closeEditor) throws CoreException, BadLocationException {
      // Select statement in debug tree
      SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, pathToStatementInTree);
      // Get statement that should be selected in opened editor.
      ISEDStatement statement = (ISEDStatement)TestUtilsUtil.getTreeItemData(item);
      // Make sure that an editor is opened
      SWTBotEditor editor = TestUtilsUtil.waitForEditor(bot);
      assertNotNull(editor);
      assertEquals(1, bot.editors().size());
      // Make sure that the correct editor is opened
      IEditorPart editorPart = editor.getReference().getEditor(true);
      TestSedCoreUtil.assertDebugEditor(editorPart, method.getResource(), target, statement);
      // Make sure that the correct line is annotated in the editor
      TestSedCoreUtil.assertDebugCodeAnnotation(editorPart, statement);
      // Close editor
      if (closeEditor) {
         editor.close();
      }
   }
   
   /**
    * Tests the lookup requests in
    * {@link KeYSourceLookupParticipant}, {@link KeYSourceLookupDirector} and
    * {@link ILaunch}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testLookupRequests() throws Exception {
      // Create bot
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      // Get current settings to restore them in finally block
      IPerspectiveDescriptor defaultPerspective = TestUtilsUtil.getActivePerspective();
      SWTBotTree debugTree = null;
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      try {
         // Open symbolic debug perspective
         TestSedCoreUtil.openSymbolicDebugPerspective();
         // Create test project
         IJavaProject project = TestUtilsUtil.createJavaProject("SWTBotKeYSourceLookupParticipantTest_testLookupRequests");
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/statements", project.getProject().getFolder("src"));
         // Get method
         IMethod method = TestUtilsUtil.getJdtMethod(project, "FlatSteps", "doSomething", "I", "QString;", "Z");
         // Increase timeout
         SWTBotPreferences.TIMEOUT = SWTBotPreferences.TIMEOUT * 8;
         // Launch method
         TestSEDKeyCoreUtil.launchKeY(method, null, null, Boolean.FALSE, Boolean.FALSE, Boolean.FALSE, Boolean.FALSE, Boolean.FALSE, Boolean.FALSE, Boolean.TRUE);
         // Find the launched ILaunch in the debug view
         SWTBotView debugView = TestSedCoreUtil.getDebugView(bot);
         debugTree = debugView.bot().tree();
         ISEDDebugTarget target = TestSedCoreUtil.waitUntilDebugTreeHasDebugTarget(bot, debugTree);
         ILaunch launch = target.getLaunch();
         // Click on "Resume" and wait until step was executed.
         final SWTBotTreeItem item = TestUtilsUtil.selectInTree(debugTree, 0, 0); // Select first debug target
         DebugTargetResumeSuspendListener.run(bot, target, new Runnable() {
            @Override
            public void run() {
               SWTBotMenu menuItem = item.contextMenu("Resume"); 
               menuItem.click();
            }
         });
         // Test the execution tree
         TestSEDKeyCoreUtil.assertFlatStepsExample(target);
         // Get stack frame for lookup
         assertEquals(1, target.getSymbolicThreads().length);
         ISEDThread thread = target.getSymbolicThreads()[0];
         assertTrue(thread.getChildren().length >= 1);
         assertTrue(thread.getChildren()[0] instanceof ISEDMethodCall);
         ISEDMethodCall call = (ISEDMethodCall)thread.getChildren()[0];
         assertTrue(call.getChildren().length >= 1);
         assertTrue(call.getChildren()[0] instanceof ISEDStatement);
         ISEDStatement s1 = (ISEDStatement)call.getChildren()[0];
         // Test KeYSourceLookupParticipant directly
         KeYSourceLookupParticipant participant = new KeYSourceLookupParticipant();
         assertEquals(File.separator + method.getResource().getName(), participant.getSourceName(s1));
         // Test KeYSourceLookupDirector directly
         KeYSourceLookupDirector director = new KeYSourceLookupDirector();
         director.initializeDefaults(launch.getLaunchConfiguration());
         assertEquals(method.getResource(), director.getSourceElement((IStackFrame)s1));
         assertEquals(method.getResource(), director.getSourceElement((Object)s1));
         // Test overall process
         ISourceLocator locator = launch.getSourceLocator();
         Object element = locator.getSourceElement(s1);
         assertEquals(method.getResource(), element);
      }
      finally {
         // Restore timeout
         SWTBotPreferences.TIMEOUT = originalTimeout;
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
         // Restore perspective
         TestUtilsUtil.openPerspective(defaultPerspective);
      }
   }
}