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

package org.key_project.sed.core.test.util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertNotNull;

import java.io.File;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.core.model.IDebugElement;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.core.model.IDisconnect;
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.debug.core.model.IThread;
import org.eclipse.debug.core.model.IValue;
import org.eclipse.debug.core.model.IVariable;
import org.eclipse.debug.core.sourcelookup.containers.LocalFileStorage;
import org.eclipse.debug.internal.ui.DebugUIPlugin;
import org.eclipse.debug.internal.ui.DelegatingModelPresentation;
import org.eclipse.debug.internal.ui.InstructionPointerManager;
import org.eclipse.debug.ui.DebugUITools;
import org.eclipse.debug.ui.IDebugModelPresentation;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.SWTBot;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.waits.ICondition;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.eclipse.ui.IViewReference;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.navigator.resources.ProjectExplorer;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.texteditor.ITextEditor;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDBranchStatement;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDExceptionalTermination;
import org.key_project.sed.core.model.ISEDLoopBodyTermination;
import org.key_project.sed.core.model.ISEDLoopCondition;
import org.key_project.sed.core.model.ISEDLoopInvariant;
import org.key_project.sed.core.model.ISEDLoopStatement;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodContract;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.ISEDValue;
import org.key_project.sed.core.util.ISEDIterator;
import org.key_project.sed.core.util.LaunchUtil;
import org.key_project.sed.core.util.SEDPreferenceUtil;
import org.key_project.sed.core.util.SEDPreorderIterator;
import org.key_project.sed.ui.perspective.SymbolicDebugPerspectiveFactory;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.java.thread.AbstractRunnableWithException;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithException;
import org.key_project.util.java.thread.IRunnableWithResult;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Provides static methods that makes testing easier
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public final class TestSedCoreUtil {
   /**
    * The ID of the fixed example launch configuration type.
    */
   public static final String FIXED_EXAMPLE_LAUNCH_CONFIGURATION_TYPE_ID = "org.key_project.sed.core.test.example.fixed_launch_content";

   /**
    * The launch mode supported by the fixed example.
    */
   public static final String FIXED_EXAMPLE_MODE = "debug";
   
   /**
    * Forbid instances.
    */
   private TestSedCoreUtil() {
   }
   
   /**
    * Returns the {@link ILaunchConfigurationType} of the fixed example.
    * @return The {@link ILaunchConfigurationType} of the fixed example.
    */
   public static ILaunchConfigurationType getFixedExampleConfigurationType() {
       return LaunchUtil.getConfigurationType(FIXED_EXAMPLE_LAUNCH_CONFIGURATION_TYPE_ID);            
   }
   
   /**
    * Creates a new fixed example {@link ILaunchConfiguration}.
    * @return The created {@link ILaunchConfiguration}.
    * @throws CoreException Occurred Exception.
    */
   public static ILaunchConfiguration createFixedExampleLaunchConfiguration() throws CoreException {
      ILaunchConfiguration config = null;
      ILaunchConfigurationWorkingCopy wc = null;
      ILaunchConfigurationType configType = getFixedExampleConfigurationType();
      wc = configType.newInstance(null, LaunchUtil.getLaunchManager().generateLaunchConfigurationName("Fixed Example Test"));
      config = wc.doSave();
      return config;
   }
   
   /**
    * Returns all existing {@link ILaunchConfiguration} of the fixed example.
    * @return All existing {@link ILaunchConfiguration}s.
    * @throws CoreException Occurred Exception.
    */
   public static ILaunchConfiguration[] searchFixedExampleLaunchConfigurations() throws CoreException {
       return DebugPlugin.getDefault().getLaunchManager().getLaunchConfigurations(getFixedExampleConfigurationType());
   }
   
   /**
    * Returns an {@link ILaunchConfiguration} of the fixed example to execute.
    * @return The {@link ILaunchConfiguration} to execute.
    * @throws CoreException Occurred Exception.
    */
   public static ILaunchConfiguration getFixedExampleLaunchConfiguration() throws CoreException {
      ILaunchConfiguration[] existingConfigs = searchFixedExampleLaunchConfigurations();
      if (existingConfigs != null && existingConfigs.length >= 1) {
         return existingConfigs[0];
      }
      else {
         return createFixedExampleLaunchConfiguration();
      }
   }
   
   /**
    * Launches the fixed example.
    * @throws Exception Occurred Exception.
    */
   public static void launchFixedExample() throws Exception {
      IRunnableWithException run = new AbstractRunnableWithException() {
         @Override
         public void run() {
            try {
               ILaunchConfiguration config = getFixedExampleLaunchConfiguration();
               DebugUITools.launch(config, FIXED_EXAMPLE_MODE);
            }
            catch (Exception e) {
               setException(e);
            }
         }
      };
      Display.getDefault().syncExec(run);
      if (run.getException() != null) {
         throw run.getException();
      }
   }

   /**
    * Opens the "Symbolic Debug" perspective.
    * @return The {@link IPerspectiveDescriptor} of "Symbolic Debug" perspective.
    * @throws Exception Occurred Exception.
    */
   public static IPerspectiveDescriptor openSymbolicDebugPerspective() throws Exception {
      IRunnableWithResult<IPerspectiveDescriptor> run = new AbstractRunnableWithResult<IPerspectiveDescriptor>() {
         @Override
         public void run() {
            try {
               // Make sure that the view is not already opened
               IWorkbenchPage activePage = WorkbenchUtil.getActivePage();
               TestCase.assertNotNull(activePage);
               if (activePage.getPerspective() == null || !ObjectUtil.equals(activePage.getPerspective().getId(), SymbolicDebugPerspectiveFactory.PERSPECTIVE_ID)) {
                  // Make sure that the project explorer is not active to avoid NullPointerException in constructor of org.eclipse.ui.internal.navigator.resources.workbench.TabbedPropertySheetTitleProvider
                  IWorkbenchPart part = activePage.findView(ProjectExplorer.VIEW_ID);
                  if (WorkbenchUtil.isActive(part)) {
                     // Project explorer is active, so select another view if possible
                     IViewReference[] viewRefs = activePage.getViewReferences();
                     boolean done = false;
                     int i = 0;
                     while (!done && i < viewRefs.length) {
                        if (!ObjectUtil.equals(viewRefs[i].getId(), ProjectExplorer.VIEW_ID)) {
                           WorkbenchUtil.activate(viewRefs[i].getView(true));
                           done = true;
                        }
                        i++;
                     }
                  }
                  // Change perspective
                  String perspectiveId = SymbolicDebugPerspectiveFactory.PERSPECTIVE_ID;
                  IPerspectiveDescriptor perspective = PlatformUI.getWorkbench().getPerspectiveRegistry().findPerspectiveWithId(perspectiveId);
                  TestCase.assertNotNull(perspective);
                  activePage.setPerspective(perspective);
                  // Make sure that correct perspective is open
                  TestCase.assertEquals(perspective, activePage.getPerspective());
               }
            }
            catch (Exception e) {
               setException(e);
            }
            catch (Throwable t) {
               setException(new Exception(t));
            }
         }
      };
      Display.getDefault().syncExec(run);
      if (run.getException() != null) {
         throw run.getException();
      }
      return run.getResult();
   }

   /**
    * Returns the {@link SWTBotView} for the debug view.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @return The {@link SWTBotView}.
    */
   public static SWTBotView getDebugView(SWTWorkbenchBot bot) {
      return bot.viewById(IDebugUIConstants.ID_DEBUG_VIEW);
   }

   /**
    * Returns the {@link SWTBotView} for the variables view.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @return The {@link SWTBotView}.
    */
   public static SWTBotView getVariablesView(SWTWorkbenchBot bot) {
      return bot.viewById(IDebugUIConstants.ID_VARIABLE_VIEW);
   }

   /**
    * Makes sure that only the fixed example is shown in the given {@link SWTBotTree}.
    * @param debugTree The {@link SWTBotTree} to check.
    */
   public static void assertFixedExample(SWTBotTree debugTree) {
      // Assert launch
      SWTBotTreeItem[] launchItems = debugTree.getAllItems();
      TestCase.assertEquals(1, launchItems.length);
      TestCase.assertEquals("Fixed Example Test [Fixed Example]", launchItems[0].getText());
      // Assert target
      SWTBotTreeItem[] targetItems = launchItems[0].getItems();
      TestCase.assertEquals(1, targetItems.length);
      TestCase.assertEquals("Fixed Example Target", targetItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(targetItems[0]) instanceof ISEDDebugTarget);
      // Assert thread
      SWTBotTreeItem[] threadItems = targetItems[0].getItems();
      TestCase.assertEquals(1, threadItems.length);
      TestCase.assertEquals("Fixed Example Thread", threadItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(threadItems[0]) instanceof ISEDThread);
      // Assert statement1
      SWTBotTreeItem[] statement1Items = threadItems[0].getItems();
      TestCase.assertEquals(1, statement1Items.length);
      TestCase.assertEquals("int x = 1;", statement1Items[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statement1Items[0]) instanceof ISEDStatement);
      // Assert loop statement
      SWTBotTreeItem[] loopNodeItems = statement1Items[0].getItems();
      TestCase.assertEquals(1, loopNodeItems.length);
      TestCase.assertEquals("while (x == 1)", loopNodeItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(loopNodeItems[0]) instanceof ISEDLoopStatement);
      // Assert loop condition
      SWTBotTreeItem[] loopConditionItems = loopNodeItems[0].getItems();
      TestCase.assertEquals(1, loopConditionItems.length);
      TestCase.assertEquals("x == 1", loopConditionItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(loopConditionItems[0]) instanceof ISEDLoopCondition);
      // Assert loop statement
      SWTBotTreeItem[] loopStatementItems = loopConditionItems[0].getItems();
      TestCase.assertEquals(1, loopStatementItems.length);
      TestCase.assertEquals("x++;", loopStatementItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(loopStatementItems[0]) instanceof ISEDStatement);
      // Assert statement2
      SWTBotTreeItem[] statement2Items = loopStatementItems[0].getItems();
      TestCase.assertEquals(1, statement2Items.length);
      TestCase.assertEquals("int y = 2;", statement2Items[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statement2Items[0]) instanceof ISEDStatement);
      // Assert statement3
      SWTBotTreeItem[] statement3Items = statement2Items[0].getItems();
      TestCase.assertEquals(1, statement3Items.length);
      TestCase.assertEquals("int result = (x + y) / z;", statement3Items[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statement3Items[0]) instanceof ISEDStatement);
      // Assert branch conditions
      SWTBotTreeItem[] conditions1Items = statement3Items[0].getItems();
      TestCase.assertEquals(2, conditions1Items.length);
      TestCase.assertEquals("z == 0", conditions1Items[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(conditions1Items[0]) instanceof ISEDBranchCondition);
      TestCase.assertEquals("z != 0", conditions1Items[1].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(conditions1Items[1]) instanceof ISEDBranchCondition);
      // Assert branch zero
      SWTBotTreeItem[] branchZeroItems = conditions1Items[0].getItems();
      TestCase.assertEquals(1, branchZeroItems.length);
      TestCase.assertEquals("throws DivisionByZeroException()", branchZeroItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(branchZeroItems[0]) instanceof ISEDExceptionalTermination);
      // Assert branch not zero
      SWTBotTreeItem[] branchNotZeroItems = conditions1Items[1].getItems();
      TestCase.assertEquals(1, branchNotZeroItems.length);
      TestCase.assertEquals("foo(result)", branchNotZeroItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(branchNotZeroItems[0]) instanceof ISEDMethodCall);
      // Assert method call
      SWTBotTreeItem[] callItems = branchNotZeroItems[0].getItems();
      TestCase.assertEquals(1, callItems.length);
      TestCase.assertEquals("if (result >= 0)", callItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(callItems[0]) instanceof ISEDBranchStatement);
      // Assert branch conditions
      SWTBotTreeItem[] conditions2Items = callItems[0].getItems();
      TestCase.assertEquals(2, conditions2Items.length);
      TestCase.assertEquals("result < 0", conditions2Items[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(conditions2Items[0]) instanceof ISEDBranchCondition);
      TestCase.assertEquals("result >= 0", conditions2Items[1].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(conditions2Items[1]) instanceof ISEDBranchCondition);
      // Assert branch negative
      SWTBotTreeItem[] negativeItems = conditions2Items[0].getItems();
      TestCase.assertEquals(1, negativeItems.length);
      TestCase.assertEquals("return -1", negativeItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(negativeItems[0]) instanceof ISEDMethodReturn);
      // Assert termination negative
      SWTBotTreeItem[] negativeTerminationItems = negativeItems[0].getItems();
      TestCase.assertEquals(1, negativeTerminationItems.length);
      TestCase.assertEquals("<end>", negativeTerminationItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(negativeTerminationItems[0]) instanceof ISEDTermination);
      // Assert termination negative empty
      SWTBotTreeItem[] negativeTerminationEmptyItems = negativeTerminationItems[0].getItems();
      TestCase.assertEquals(0, negativeTerminationEmptyItems.length);
      // Assert branch positive
      SWTBotTreeItem[] positiveItems = conditions2Items[1].getItems();
      TestCase.assertEquals(1, positiveItems.length);
      TestCase.assertEquals("return 1", positiveItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(positiveItems[0]) instanceof ISEDMethodReturn);
      // Assert termination positive
      SWTBotTreeItem[] positiveTerminationItems = positiveItems[0].getItems();
      TestCase.assertEquals(1, positiveTerminationItems.length);
      TestCase.assertEquals("<loop body end>", positiveTerminationItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(positiveTerminationItems[0]) instanceof ISEDTermination);
      // Assert termination positive empty
      SWTBotTreeItem[] positiveTerminationEmptyItems = positiveTerminationItems[0].getItems();
      TestCase.assertEquals(0, positiveTerminationEmptyItems.length);
   }

   /**
    * Makes sure that only the fixed example is shown in compact view
    * in the given {@link SWTBotTree}.
    * @param debugTree The {@link SWTBotTree} to check.
    */
   public static void assertCompactFixedExample(SWTBotTree debugTree) {
      // Assert launch
      SWTBotTreeItem[] launchItems = debugTree.getAllItems();
      TestCase.assertEquals(1, launchItems.length);
      TestCase.assertEquals("Fixed Example Test [Fixed Example]", launchItems[0].getText());
      // Assert target
      SWTBotTreeItem[] targetItems = launchItems[0].getItems();
      TestCase.assertEquals(1, targetItems.length);
      TestCase.assertEquals("Fixed Example Target", targetItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(targetItems[0]) instanceof ISEDDebugTarget);
      // Assert thread
      SWTBotTreeItem[] threadItems = targetItems[0].getItems();
      TestCase.assertEquals(1, threadItems.length);
      TestCase.assertEquals("Fixed Example Thread", threadItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(threadItems[0]) instanceof ISEDThread);
      // Assert statement1, loop statement, loop condition, loop statement, statement 2 and 3
      SWTBotTreeItem[] statementItems = threadItems[0].getItems();
      TestCase.assertEquals(6, statementItems.length);
      TestCase.assertEquals("int x = 1;", statementItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statementItems[0]) instanceof ISEDStatement);
      TestCase.assertEquals(0, statementItems[0].getItems().length);

      TestCase.assertEquals("while (x == 1)", statementItems[1].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statementItems[1]) instanceof ISEDLoopStatement);
      TestCase.assertEquals(0, statementItems[1].getItems().length);
      TestCase.assertEquals("x == 1", statementItems[2].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statementItems[2]) instanceof ISEDLoopCondition);
      TestCase.assertEquals(0, statementItems[2].getItems().length);
      TestCase.assertEquals("x++;", statementItems[3].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statementItems[3]) instanceof ISEDStatement);
      TestCase.assertEquals(0, statementItems[3].getItems().length);
      
      TestCase.assertEquals("int y = 2;", statementItems[4].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statementItems[4]) instanceof ISEDStatement);
      TestCase.assertEquals(0, statementItems[4].getItems().length);
      TestCase.assertEquals("int result = (x + y) / z;", statementItems[5].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statementItems[5]) instanceof ISEDStatement);
      // Assert branch conditions
      SWTBotTreeItem[] conditions1Items = statementItems[5].getItems();
      TestCase.assertEquals(2, conditions1Items.length);
      TestCase.assertEquals("z == 0", conditions1Items[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(conditions1Items[0]) instanceof ISEDBranchCondition);
      TestCase.assertEquals("z != 0", conditions1Items[1].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(conditions1Items[1]) instanceof ISEDBranchCondition);
      // Assert branch zero
      SWTBotTreeItem[] branchZeroItems = conditions1Items[0].getItems();
      TestCase.assertEquals(1, branchZeroItems.length);
      TestCase.assertEquals("throws DivisionByZeroException()", branchZeroItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(branchZeroItems[0]) instanceof ISEDExceptionalTermination);
      // Assert branch not zero
      SWTBotTreeItem[] branchNotZeroItems = conditions1Items[1].getItems();
      TestCase.assertEquals(2, branchNotZeroItems.length);
      TestCase.assertEquals("foo(result)", branchNotZeroItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(branchNotZeroItems[0]) instanceof ISEDMethodCall);
      TestCase.assertEquals(0, branchNotZeroItems[0].getItems().length);
      TestCase.assertEquals("if (result >= 0)", branchNotZeroItems[1].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(branchNotZeroItems[1]) instanceof ISEDBranchStatement);
      // Assert branch conditions
      SWTBotTreeItem[] conditions2Items = branchNotZeroItems[1].getItems();
      TestCase.assertEquals(2, conditions2Items.length);
      TestCase.assertEquals("result < 0", conditions2Items[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(conditions2Items[0]) instanceof ISEDBranchCondition);
      TestCase.assertEquals("result >= 0", conditions2Items[1].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(conditions2Items[1]) instanceof ISEDBranchCondition);
      // Assert branch negative
      SWTBotTreeItem[] negativeItems = conditions2Items[0].getItems();
      TestCase.assertEquals(2, negativeItems.length);
      TestCase.assertEquals("return -1", negativeItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(negativeItems[0]) instanceof ISEDMethodReturn);
      TestCase.assertEquals(0, negativeItems[0].getItems().length);
      TestCase.assertEquals("<end>", negativeItems[1].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(negativeItems[1]) instanceof ISEDTermination);
      TestCase.assertEquals(0, negativeItems[1].getItems().length);
      // Assert branch positive
      SWTBotTreeItem[] positiveItems = conditions2Items[1].getItems();
      TestCase.assertEquals(2, positiveItems.length);
      TestCase.assertEquals("return 1", positiveItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(positiveItems[0]) instanceof ISEDMethodReturn);
      TestCase.assertEquals(0, positiveItems[0].getItems().length);
      TestCase.assertEquals("<loop body end>", positiveItems[1].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(positiveItems[1]) instanceof ISEDTermination);
      TestCase.assertEquals(0, positiveItems[1].getItems().length);
   }

   /**
    * Terminates and removes all {@link ILaunch}s in the given tree.
    * @param debugTree The given tree.
    */
   public static void terminateAndRemoveAll(SWTBotTree debugTree) {
      if (debugTree!= null) {
         SWTWorkbenchBot bot = new SWTWorkbenchBot();
         // Terminate all items
         SWTBotTreeItem[] launchItems = debugTree.getAllItems();
         for (SWTBotTreeItem item : launchItems) {
            item.select();
            item.contextMenu("Terminate and Remove").click();
            try{
               SWTBotShell dialog = bot.shell("Terminate and Remove");
               dialog.bot().button("Yes").click();
            }catch(Exception e){
            }
         }
         // Wait until all items are removed
         bot.waitWhile(Conditions.treeHasRows(debugTree, 1));
         // Make sure that the tree has no items
         launchItems = debugTree.getAllItems();
         TestCase.assertEquals(0, launchItems.length);
      }
   }

   /**
    * Waits until the given value is defined for {@link SEDPreferenceUtil#isShowCompactExecutionTree()}.
    * @param bot The {@link SWTBot} to use.
    * @param value The value to wait for.
    */
   public static void waitUntilShowCompactExecutionTreeValue(SWTBot bot, final boolean value) {
      bot.waitUntil(new ICondition() {
         @Override
         public boolean test() throws Exception {
            return value == SEDPreferenceUtil.isShowCompactExecutionTree();
         }
         
         @Override
         public void init(SWTBot bot) {
         }
         
         @Override
         public String getFailureMessage() {
            return "The show symbolic compact execution tree value is not " + value + ".";
         }
      });
   }

   /**
    * Returns the first available {@link ILaunch} in the given debug tree.
    * @param debugTree The given debug tree.
    * @return The first available {@link ILaunch}.
    */
   public static ILaunch getFirstLaunch(SWTBotTree debugTree) {
      SWTBotTreeItem[] items = debugTree.getAllItems();
      if (items.length >= 1) {
         Object object = TestUtilsUtil.getTreeItemData(items[0]);
         TestCase.assertTrue(object instanceof ILaunch);
         return (ILaunch)object;
      }
      else {
         TestCase.fail("Debug tree is empty.");
         return null;
      }
   }

   /**
    * Waits until the given {@link SWTBotTree} contains at least one {@link ISEDDebugTarget}.
    * @param bot The {@link SWTBot} to use.
    * @param debugTree The {@link SWTBotTree} to search in.
    * @return The first found {@link ISEDDebugTarget}.
    */
   public static ISEDDebugTarget waitUntilDebugTreeHasDebugTarget(SWTBot bot, final SWTBotTree debugTree) {
      WaitForDebugTargetCondition condition = new WaitForDebugTargetCondition(debugTree);
      bot.waitUntil(condition);
      return condition.getTarget();
   }
   
   /**
    * {@link ICondition} to receive the first {@link IDebugTarget} in a given {@link SWTBotTree}.
    * @author Martin Hentschel
    */
   private static class WaitForDebugTargetCondition implements ICondition {
      /**
       * The {@link SWTBotTree} to search in.
       */
      private SWTBotTree debugTree;
      
      /**
       * The found {@link ISEDDebugTarget}.
       */
      private ISEDDebugTarget target; 
      
      /**
       * Constructor.
       * @param debugTree The {@link SWTBotTree} to search in.
       */
      public WaitForDebugTargetCondition(SWTBotTree debugTree) {
         TestCase.assertNotNull(debugTree);
         this.debugTree = debugTree;
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public boolean test() throws Exception {
         IRunnableWithResult<Boolean> run = new AbstractRunnableWithResult<Boolean>() {
            @Override
            public void run() {
               setResult(Boolean.FALSE);
               TreeItem[] rootItems = debugTree.widget.getItems();
               if (rootItems != null && rootItems.length >= 1) {
                  TreeItem[] level1Items = rootItems[0].getItems();
                  if (level1Items != null && level1Items.length >= 1) {
                     Object data = level1Items[0].getData();
                     if (data instanceof ISEDDebugTarget) {
                        target = (ISEDDebugTarget)data;
                        setResult(Boolean.TRUE);
                     }
                  }
               }
            }
         };
         debugTree.display.syncExec(run);
         return run.getResult() != null && run.getResult().booleanValue();
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void init(SWTBot bot) {
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public String getFailureMessage() {
         return "Debug tree has no IDebugTarget.";
      }

      /**
       * Returns the found {@link ISEDDebugTarget}.
       * @return The found {@link ISEDDebugTarget}.
       */
      public ISEDDebugTarget getTarget() {
         return target;
      }
   }

   /**
    * Waits until the given {@link ILaunch} is terminated.
    * @param bot The {@link SWTBot} to use.
    * @param launch The {@link ILaunch} to wait for.
    */
   public static void waitUntilLaunchIsTerminated(SWTBot bot, final ILaunch launch) {
      TestCase.assertNotNull(bot);
      TestCase.assertNotNull(launch);
      bot.waitUntil(new ICondition() {
         @Override
         public boolean test() throws Exception {
            return launch.isTerminated();
         }
         
         @Override
         public void init(SWTBot bot) {
         }
         
         @Override
         public String getFailureMessage() {
            return "ILaunch \"" + launch + "\" is not terminated.";
         }
      });
   }
   
   /**
    * Waits until the given {@link IDisconnect} is terminated.
    * @param bot The {@link SWTBot} to use.
    * @param disconnect The {@link IDisconnect} to wait for.
    */
   public static void waitUntilLaunchIsDisconnected(SWTBot bot, final IDisconnect disconnect) {
      TestCase.assertNotNull(bot);
      TestCase.assertNotNull(disconnect);
      bot.waitUntil(new ICondition() {
         @Override
         public boolean test() throws Exception {
            return disconnect.isDisconnected();
         }
         
         @Override
         public void init(SWTBot bot) {
         }
         
         @Override
         public String getFailureMessage() {
            return "ILaunch \"" + disconnect + "\" is not terminated.";
         }
      });
   }

   /**
    * Waits until the {@link IDebugTarget} can suspend.
    * @param bot The {@link SWTBot} to use.
    * @param target The {@link ISEDDebugTarget} to wait for.
    */
   public static void waitUntilDebugTargetCanSuspend(SWTBot bot, final ISEDDebugTarget target) {
      TestCase.assertNotNull(bot);
      TestCase.assertNotNull(target);
      bot.waitUntil(new ICondition() {
         @Override
         public boolean test() throws Exception {
            return target.canSuspend();
         }
         
         @Override
         public void init(SWTBot bot) {
         }
         
         @Override
         public String getFailureMessage() {
            return "ISEDDebugTarget \"" + target + "\" can not suspend.";
         }
      }, SWTBotPreferences.TIMEOUT, 0); // Delay must be very short because otherwise it is possible that the auto mode has finished between checks which results in a timeout exception.
   }

   /**
    * Waits until the {@link IDebugTarget} can resume.
    * @param bot The {@link SWTBot} to use.
    * @param target The {@link ISEDDebugTarget} to wait for.
    */
   public static void waitUntilDebugTargetCanResume(SWTBot bot, final ISEDDebugTarget target) {
      TestCase.assertNotNull(bot);
      TestCase.assertNotNull(target);
      bot.waitUntil(new ICondition() {
         @Override
         public boolean test() throws Exception {
            return target.canResume();
         }
         
         @Override
         public void init(SWTBot bot) {
         }
         
         @Override
         public String getFailureMessage() {
            return "ISEDDebugTarget \"" + target + "\" can not resume.";
         }
      });
   }

   /**
    * Makes sure that the correct {@link IEditorPart} was opened by the 
    * Eclipse Debug API.
    * @param currentEditorPart The current {@link IEditorPart} to test.
    * @param expectedResource The expected {@link IResource}.
    * @param target The {@link IDebugTarget} to use.
    * @param frame The {@link IStackFrame} to test.
    * @throws PartInitException Occurred Exception.
    */
   public static void assertDebugEditor(IEditorPart currentEditorPart, 
                                        IResource expectedResource,
                                        IDebugTarget target, 
                                        IStackFrame frame) throws PartInitException {
      IDebugModelPresentation presentation = ((DelegatingModelPresentation)DebugUIPlugin.getModelPresentation()).getPresentation(target.getModelIdentifier());
      Object sourceElement = target.getLaunch().getSourceLocator().getSourceElement(frame);
      TestCase.assertEquals(expectedResource, sourceElement);
      IEditorInput expectedInput = presentation.getEditorInput(sourceElement);
      TestCase.assertEquals(expectedInput, currentEditorPart.getEditorInput());
      String expectedId = presentation.getEditorId(expectedInput, frame);
      TestCase.assertEquals(expectedId, currentEditorPart.getEditorSite().getId());
      TestCase.assertEquals(expectedResource, currentEditorPart.getEditorInput().getAdapter(IResource.class));
   }

   /**
    * Makes sure that the correct {@link IEditorPart} was opened by the 
    * Eclipse Debug API.
    * @param currentEditorPart The current {@link IEditorPart} to test.
    * @param expectedFile The expected {@link File}.
    * @param target The {@link IDebugTarget} to use.
    * @param frame The {@link IStackFrame} to test.
    * @throws PartInitException Occurred Exception.
    */
   public static void assertDebugEditor(IEditorPart currentEditorPart, 
                                        File expectedFile,
                                        IDebugTarget target, 
                                        IStackFrame frame) {
      IDebugModelPresentation presentation = ((DelegatingModelPresentation)DebugUIPlugin.getModelPresentation()).getPresentation(target.getModelIdentifier());
      Object sourceElement = target.getLaunch().getSourceLocator().getSourceElement(frame);
      TestCase.assertTrue(sourceElement instanceof LocalFileStorage);
      TestCase.assertEquals(expectedFile, ((LocalFileStorage)sourceElement).getFile());
      IEditorInput expectedInput = presentation.getEditorInput(sourceElement);
      TestCase.assertEquals(expectedInput, currentEditorPart.getEditorInput());
      String expectedId = presentation.getEditorId(expectedInput, frame);
      TestCase.assertEquals(expectedId, currentEditorPart.getEditorSite().getId());
   }
   
   /**
    * Makes sure that the given {@link IEditorPart} is an {@link ITextEditor}
    * which has a {@link Annotation} for the given {@link IStackFrame}.
    * For more details have a look at class {@link InstructionPointerManager}.
    * @param editorPart The {@link IEditorPart} to test.
    * @param frame The {@link IStackFrame} that should have an annotation.
    * @throws CoreException Occurred Exception.
    * @throws BadLocationException Occurred Exception.
    */
   public static void assertDebugCodeAnnotation(IEditorPart editorPart, IStackFrame frame) throws CoreException, BadLocationException {
      TestCase.assertTrue(editorPart instanceof ITextEditor);
      IEditorInput input = editorPart.getEditorInput();
      ITextEditor textEditor = (ITextEditor)editorPart;
      IDocumentProvider provider = textEditor.getDocumentProvider();
      try {
         provider.connect(input);
         IDocument document = provider.getDocument(editorPart.getEditorInput());
         IAnnotationModel annotationModel = provider.getAnnotationModel(editorPart.getEditorInput());
         Annotation annotation = ((DelegatingModelPresentation)DebugUIPlugin.getModelPresentation()).getInstructionPointerAnnotation(editorPart, frame);
         TestCase.assertNotNull(annotation);
         Position position = annotationModel.getPosition(annotation);
         TestCase.assertNotNull(position);
         if (frame.getCharStart() >= 0) {
            TestCase.assertEquals(frame.getCharStart(), position.getOffset());
            TestCase.assertEquals(frame.getCharEnd() - frame.getCharStart(), position.getLength());
         }
         else {
            TestCase.assertEquals(frame.getLineNumber() - 1, document.getLineOfOffset(position.getOffset()));
         }
      }
      finally {
         provider.disconnect(input);
      }
   }

   /**
    * Suspends the given {@link ISEDDebugTarget} as soon as possible.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param target The {@link ISEDDebugTarget} to suspend.
    */
   public static void suspend(SWTWorkbenchBot bot, final ISEDDebugTarget target) {
      TestCase.assertNotNull(bot);
      TestCase.assertNotNull(target);
      bot.waitUntil(new ICondition() {
         @Override
         public synchronized boolean test() throws Exception {
            if (target.canSuspend()) {
               target.suspend();
               return true;
            }
            else {
               return false;
            }
         }
         
         @Override
         public void init(SWTBot bot) {
         }
         
         @Override
         public String getFailureMessage() {
            return "ISEDDebugTarget \"" + target + "\" can not suspend.";
         }
      }, SWTBotPreferences.TIMEOUT, 0); // Delay must be very short because otherwise it is possible that the auto mode has finished between checks which results in a timeout exception.
   }

   /**
    * Compares the given {@link ISEDDebugTarget}s with each other.
    * @param expected The expected {@link ISEDDebugTarget}.
    * @param current The current {@link ISEDDebugTarget}.
    * @param compareId Compare the value of {@link ISEDDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @throws DebugException Occurred Exception.
    */
   public static void compareDebugTarget(ISEDDebugTarget expected, 
                                         ISEDDebugTarget current, 
                                         boolean compareId, 
                                         boolean compareVariables,
                                         boolean compareCallStack) throws DebugException {
      // Compare annotations
      ISEDAnnotation[] expectedAnnotations = expected.getRegisteredAnnotations();
      ISEDAnnotation[] currentAnnotations = current.getRegisteredAnnotations();
      assertEquals(expectedAnnotations.length, currentAnnotations.length);
      for (int i = 0; i < expectedAnnotations.length; i++) {
         compareAnnotation(expectedAnnotations[i], currentAnnotations[i]);
      }
      // Compare nodes
      ISEDIterator expectedIter = new SEDPreorderIterator(expected);
      ISEDIterator currentIter = new SEDPreorderIterator(current);
      while (expectedIter.hasNext()) {
         TestCase.assertTrue(currentIter.hasNext());
         ISEDDebugElement expectedNext = expectedIter.next();
         ISEDDebugElement currentNext = currentIter.next();
         if (expectedNext instanceof ISEDDebugTarget) {
            TestCase.assertTrue("Expected ISEDDebugTarget on " + ((ISEDDebugTarget)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEDDebugTarget);
            compareDebugElement(expectedNext, currentNext, true, compareId);
            compareDebugTarget((IDebugTarget)expectedNext, (IDebugTarget)currentNext, true, compareVariables);
         }
         else if (expectedNext instanceof ISEDBranchCondition) {
            TestCase.assertTrue("Expected ISEDBranchCondition on " + ((ISEDBranchCondition)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEDBranchCondition);
            compareBranchCondition((ISEDBranchCondition)expectedNext, (ISEDBranchCondition)currentNext, true, compareId, compareVariables, compareCallStack);
         }
         else if (expectedNext instanceof ISEDBranchStatement) {
            TestCase.assertTrue("Expected ISEDBranchStatement on " + ((ISEDBranchStatement)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEDBranchStatement);
            compareBranchStatement((ISEDBranchStatement)expectedNext, (ISEDBranchStatement)currentNext, true, compareId, compareVariables, compareCallStack);
         }
         else if (expectedNext instanceof ISEDExceptionalTermination) {
            TestCase.assertTrue("Expected ISEDExceptionalTermination on " + ((ISEDExceptionalTermination)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEDExceptionalTermination);
            compareExceptionalTermination((ISEDExceptionalTermination)expectedNext, (ISEDExceptionalTermination)currentNext, true, compareId, compareVariables, compareCallStack);
         }
         else if (expectedNext instanceof ISEDLoopCondition) {
            TestCase.assertTrue("Expected ISEDLoopCondition on " + ((ISEDLoopCondition)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEDLoopCondition);
            compareLoopCondition((ISEDLoopCondition)expectedNext, (ISEDLoopCondition)currentNext, true, compareId, compareVariables, compareCallStack);
         }
         else if (expectedNext instanceof ISEDLoopStatement) {
            TestCase.assertTrue("Expected ISEDLoopStatement on " + ((ISEDLoopStatement)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEDLoopStatement);
            compareLoopStatement((ISEDLoopStatement)expectedNext, (ISEDLoopStatement)currentNext, true, compareId, compareVariables, compareCallStack);
         }
         else if (expectedNext instanceof ISEDMethodCall) {
            TestCase.assertTrue("Expected ISEDMethodCall on " + ((ISEDMethodCall)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEDMethodCall);
            compareMethodCall((ISEDMethodCall)expectedNext, (ISEDMethodCall)currentNext, true, compareId, compareVariables, compareCallStack);
         }
         else if (expectedNext instanceof ISEDMethodReturn) {
            TestCase.assertTrue("Expected ISEDMethodReturn on " + ((ISEDMethodReturn)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEDMethodReturn);
            compareMethodReturn((ISEDMethodReturn)expectedNext, (ISEDMethodReturn)currentNext, true, compareId, compareVariables, compareCallStack);
         }
         else if (expectedNext instanceof ISEDStatement) {
            TestCase.assertTrue("Expected ISEDStatement on " + ((ISEDStatement)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEDStatement);
            compareStatement((ISEDStatement)expectedNext, (ISEDStatement)currentNext, true, compareId, compareVariables, compareCallStack);
         }
         else if (expectedNext instanceof ISEDTermination) {
            TestCase.assertTrue("Expected ISEDTermination on " + ((ISEDTermination)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEDTermination);
            compareTermination((ISEDTermination)expectedNext, (ISEDTermination)currentNext, true, compareId, compareVariables, compareCallStack);
         }
         else if (expectedNext instanceof ISEDThread) {
            TestCase.assertTrue("Expected ISEDThread on " + ((ISEDThread)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEDThread);
            compareThread((ISEDThread)expectedNext, (ISEDThread)currentNext, true, compareId);
         }
         else if (expectedNext instanceof ISEDMethodContract) {
            TestCase.assertTrue("Expected ISEDMethodContract on " + ((ISEDMethodContract)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEDMethodContract);
            compareMethodContract((ISEDMethodContract)expectedNext, (ISEDMethodContract)currentNext, true, compareId, compareVariables, compareCallStack);
         }
         else if (expectedNext instanceof ISEDLoopInvariant) {
            TestCase.assertTrue("Expected ISEDLoopInvariant on " + ((ISEDLoopInvariant)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEDLoopInvariant);
            compareLoopInvariant((ISEDLoopInvariant)expectedNext, (ISEDLoopInvariant)currentNext, true, compareId, compareVariables, compareCallStack);
         }
         else {
            TestCase.fail("Unknown node type \"" + (expectedNext != null ? expectedNext.getClass() : null) + "\".");
         }
      }
      TestCase.assertFalse(expectedIter.hasNext());
      TestCase.assertFalse(currentIter.hasNext());
   }
   
   /**
    * Compares the given {@link ISEDAnnotation}s with each other.
    * @param expected The expected {@link ISEDAnnotation}.
    * @param current The current {@link ISEDAnnotation}.
    */
   protected static void compareAnnotation(ISEDAnnotation expected, ISEDAnnotation current) {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.getId(), current.getId());
      TestCase.assertSame(expected.getType(), current.getType());
      TestCase.assertEquals(expected.isEnabled(), current.isEnabled());
      TestCase.assertEquals(expected.isHighlightBackground(), current.isHighlightBackground());
      TestCase.assertEquals(expected.isHighlightForeground(), current.isHighlightForeground());
      TestCase.assertEquals(expected.getBackgroundColor(), current.getBackgroundColor());
      TestCase.assertEquals(expected.getForegroundColor(), current.getForegroundColor());
      TestCase.assertEquals(expected.getType().saveAnnotation(expected), current.getType().saveAnnotation(current));
   }
   
   /**
    * Compares the given {@link ISEDAnnotationLink}s with each other.
    * @param expected The expected {@link ISEDAnnotationLink}.
    * @param current The current {@link ISEDAnnotationLink}.
    */
   protected static void compareAnnotationLink(ISEDAnnotationLink expected, ISEDAnnotationLink current) {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.getId(), current.getId());
      TestCase.assertEquals(expected.getSource().getId(), current.getSource().getId());
      TestCase.assertEquals(expected.getTarget().getId(), current.getTarget().getId());
      TestCase.assertEquals(expected.getSource().getType().saveAnnotationLink(expected), current.getSource().getType().saveAnnotationLink(current));
   }

   /**
    * Compares the given {@link IDebugTarget}s with each other.
    * @param expected The expected {@link IDebugTarget}.
    * @param current The current {@link IDebugTarget}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareVariables Compare variables?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareDebugTarget(IDebugTarget expected, IDebugTarget current, boolean compareReferences, boolean compareVariables) throws DebugException {
      // Compare debug target
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.getName(), current.getName());
      compareDebugElement(expected, current, false, compareVariables);
      // Compare debug target which should be itself
      TestCase.assertSame(expected, expected.getDebugTarget());
      TestCase.assertSame(current, current.getDebugTarget());
      if (compareReferences) {
         // Compare contained threads
         TestCase.assertEquals(expected.hasThreads(), current.hasThreads());
         IThread[] expectedThreads = expected.getThreads();
         IThread[] currentThreads = current.getThreads();
         TestCase.assertEquals(expectedThreads.length, currentThreads.length);
         for (int i = 0; i < expectedThreads.length; i++) {
            compareThread(expectedThreads[i], currentThreads[i], false, compareVariables);
         }
      }
   }
   
   /**
    * Compares the given {@link ISEDDebugNode}s with each other.
    * @param expected The expected {@link ISEDDebugNode}.
    * @param current The current {@link ISEDDebugNode}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareNode(ISEDDebugNode expected, 
                                     ISEDDebugNode current, 
                                     boolean compareReferences, 
                                     boolean compareId, 
                                     boolean compareVariables,
                                     boolean compareCallStack) throws DebugException {
      if (expected != null) {
         // Compare node
         TestCase.assertNotNull(current);
         TestCase.assertTrue(expected.getName() + " does not match " + current.getName(), StringUtil.equalIgnoreWhiteSpace(expected.getName(), current.getName()));
         TestCase.assertTrue(expected.getPathCondition() + " does not match " + current.getPathCondition(), StringUtil.equalIgnoreWhiteSpace(expected.getPathCondition(), current.getPathCondition()));
         TestCase.assertEquals(expected.getNodeType(), current.getNodeType());
         compareDebugElement(expected, current, compareReferences, compareVariables);
         // Compare annotation links
         ISEDAnnotationLink[] expectedAnnotationLinks = expected.getAnnotationLinks();
         ISEDAnnotationLink[] currentAnnotationLinks = current.getAnnotationLinks();
         assertEquals(expectedAnnotationLinks.length, currentAnnotationLinks.length);
         for (int i = 0; i < expectedAnnotationLinks.length; i++) {
            compareAnnotationLink(expectedAnnotationLinks[i], currentAnnotationLinks[i]);
         }
         // Compare call stack
         if (compareCallStack) {
            compareCallStack(expected.getCallStack(), current.getCallStack());
         }
         // Compare parent
         if (compareReferences) {
            compareNode(expected.getParent(), current.getParent(), false, compareId, compareVariables, compareCallStack);
            // Compare children
            ISEDDebugNode[] expectedChildren = expected.getChildren();
            ISEDDebugNode[] currentChildren = current.getChildren();
            TestCase.assertEquals("Number of children of " + expected + " is not equal to number of children of " + current + ".", expectedChildren.length, currentChildren.length);
            for (int i = 0; i < expectedChildren.length; i++) {
               if (expectedChildren[i] instanceof ISEDBranchCondition) {
                  TestCase.assertTrue("Expected ISEDBranchCondition on " + ((ISEDBranchCondition)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDBranchCondition);
                  compareBranchCondition((ISEDBranchCondition)expectedChildren[i], (ISEDBranchCondition)currentChildren[i], false, compareId, compareVariables, compareCallStack);
               }
               else if (expectedChildren[i] instanceof ISEDBranchStatement) {
                  TestCase.assertTrue("Expected ISEDBranchStatement on " + ((ISEDBranchStatement)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDBranchStatement);
                  compareBranchStatement((ISEDBranchStatement)expectedChildren[i], (ISEDBranchStatement)currentChildren[i], false, compareId, compareVariables, compareCallStack);
               }
               else if (expectedChildren[i] instanceof ISEDExceptionalTermination) {
                  TestCase.assertTrue("Expected ISEDExceptionalTermination on " + ((ISEDExceptionalTermination)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDExceptionalTermination);
                  compareExceptionalTermination((ISEDExceptionalTermination)expectedChildren[i], (ISEDExceptionalTermination)currentChildren[i], false, compareId, compareVariables, compareCallStack);
               }
               else if (expectedChildren[i] instanceof ISEDLoopBodyTermination) {
                  TestCase.assertTrue("Expected ISEDLoopBodyTermination on " + ((ISEDLoopBodyTermination)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDLoopBodyTermination);
                  compareLoopBodyTermination((ISEDLoopBodyTermination)expectedChildren[i], (ISEDLoopBodyTermination)currentChildren[i], false, compareId, compareVariables, compareCallStack);
               }
               else if (expectedChildren[i] instanceof ISEDLoopCondition) {
                  TestCase.assertTrue("Expected ISEDLoopCondition on " + ((ISEDLoopCondition)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDLoopCondition);
                  compareLoopCondition((ISEDLoopCondition)expectedChildren[i], (ISEDLoopCondition)currentChildren[i], false, compareId, compareVariables, compareCallStack);
               }
               else if (expectedChildren[i] instanceof ISEDLoopStatement) {
                  TestCase.assertTrue("Expected ISEDLoopStatement on " + ((ISEDLoopStatement)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDLoopStatement);
                  compareLoopStatement((ISEDLoopStatement)expectedChildren[i], (ISEDLoopStatement)currentChildren[i], false, compareId, compareVariables, compareCallStack);
               }
               else if (expectedChildren[i] instanceof ISEDLoopCondition) {
                  TestCase.assertTrue("Expected ISEDLoopCondition on " + ((ISEDLoopCondition)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDLoopCondition);
                  compareLoopCondition((ISEDLoopCondition)expectedChildren[i], (ISEDLoopCondition)currentChildren[i], false, compareId, compareVariables, compareCallStack);
               }
               else if (expectedChildren[i] instanceof ISEDLoopStatement) {
                  TestCase.assertTrue("Expected ISEDLoopStatement on " + ((ISEDLoopStatement)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDLoopStatement);
                  compareLoopStatement((ISEDLoopStatement)expectedChildren[i], (ISEDLoopStatement)currentChildren[i], false, compareId, compareVariables, compareCallStack);
               }
               else if (expectedChildren[i] instanceof ISEDMethodCall) {
                  TestCase.assertTrue("Expected ISEDMethodCall on " + ((ISEDMethodCall)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDMethodCall);
                  compareMethodCall((ISEDMethodCall)expectedChildren[i], (ISEDMethodCall)currentChildren[i], false, compareId, compareVariables, compareCallStack);
               }
               else if (expectedChildren[i] instanceof ISEDMethodReturn) {
                  TestCase.assertTrue("Expected ISEDMethodReturn on " + ((ISEDMethodReturn)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDMethodReturn);
                  compareMethodReturn((ISEDMethodReturn)expectedChildren[i], (ISEDMethodReturn)currentChildren[i], false, compareId, compareVariables, compareCallStack);
               }
               else if (expectedChildren[i] instanceof ISEDStatement) {
                  TestCase.assertTrue("Expected ISEDStatement on " + ((ISEDStatement)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDStatement);
                  compareStatement((ISEDStatement)expectedChildren[i], (ISEDStatement)currentChildren[i], false, compareId, compareVariables, compareCallStack);
               }
               else if (expectedChildren[i] instanceof ISEDTermination) {
                  TestCase.assertTrue("Expected ISEDTermination on " + ((ISEDTermination)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDTermination);
                  compareTermination((ISEDTermination)expectedChildren[i], (ISEDTermination)currentChildren[i], false, compareId, compareVariables, compareCallStack);
               }
               else if (expectedChildren[i] instanceof ISEDThread) {
                  TestCase.assertTrue("Expected ISEDThread on " + ((ISEDThread)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDThread);
                  compareThread((ISEDThread)expectedChildren[i], (ISEDThread)currentChildren[i], true, compareVariables);
               }
               else if (expectedChildren[i] instanceof ISEDMethodContract) {
                  TestCase.assertTrue("Expected ISEDMethodContract on " + ((ISEDMethodContract)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDMethodContract);
                  compareMethodContract((ISEDMethodContract)expectedChildren[i], (ISEDMethodContract)currentChildren[i], false, compareId, compareVariables, compareCallStack);
               }
               else if (expectedChildren[i] instanceof ISEDLoopInvariant) {
                  TestCase.assertTrue("Expected ISEDLoopInvariant on " + ((ISEDLoopInvariant)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEDLoopInvariant);
                  compareLoopInvariant((ISEDLoopInvariant)expectedChildren[i], (ISEDLoopInvariant)currentChildren[i], false, compareId, compareVariables, compareCallStack);
               }
               else {
                  TestCase.fail("Unknown node type \"" + (expectedChildren[i] != null ? expectedChildren[i].getClass() : null) + "\".");
               }
            }
         }
      }
      else {
         TestCase.assertNull(current);
      }
   }
   
   /**
    * Compares the given call stack entries.
    * @param expected The expected {@link ISEDDebugNode}s.
    * @param current The current {@link ISEDDebugNode}s.
    * @throws DebugException Occurred Exception.
    */
   protected static void compareCallStack(ISEDDebugNode[] expectedEntries, 
                                          ISEDDebugNode[] currentEntries) throws DebugException {
      if (expectedEntries != null) {
         TestCase.assertNotNull(currentEntries);
         TestCase.assertEquals(expectedEntries.length, currentEntries.length);
         for (int i = 0; i < expectedEntries.length; i++) {
            compareNode(expectedEntries[i], currentEntries[i], false, false, false, false);
         }
      }
      else {
         TestCase.assertTrue(ArrayUtil.isEmpty(currentEntries));
      }
   }

   /**
    * Compares the given {@link IDebugElement}s with each other.
    * @param expected The expected {@link IDebugElement}.
    * @param current The current {@link IDebugElement}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareVariables Compare variables?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareDebugElement(IDebugElement expected, IDebugElement current, boolean compareReferences, boolean compareVariables) throws DebugException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.getModelIdentifier(), current.getModelIdentifier());
      if (compareReferences) {
         if (expected.getDebugTarget() instanceof ISEDDebugTarget) {
            TestCase.assertTrue(current.getDebugTarget() instanceof ISEDDebugTarget);
            compareDebugTarget((IDebugTarget)expected.getDebugTarget(), (IDebugTarget)current.getDebugTarget(), false, compareVariables);
         }
         else {
            compareDebugTarget(expected.getDebugTarget(), current.getDebugTarget(), false, compareVariables);
         }
      }
   }
   
   /**
    * Compares the given {@link IDebugElement}s with each other.
    * @param expected The expected {@link IDebugElement}.
    * @param current The current {@link IDebugElement}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareDebugElement(ISEDDebugElement expected, ISEDDebugElement current, boolean compareReferences, boolean compareId, boolean compareVariables) throws DebugException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      if (compareId) {
         TestCase.assertEquals(expected.getId(), current.getId());
      }
      compareDebugElement((IDebugElement)expected, (IDebugElement)current, compareReferences, compareVariables);
   }
   
   /**
    * Compares the given {@link IStackFrame}s with each other.
    * @param expected The expected {@link IStackFrame}.
    * @param current The current {@link IStackFrame}.
    * @param compareVariables Compare variables?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareStackFrame(IStackFrame expected, IStackFrame current, boolean compareVariables) throws DebugException {
      if (expected != null) {
         TestCase.assertNotNull(current);
         // Compare stack frame
         TestCase.assertTrue(expected.getName() + " does not match " + current.getName(), StringUtil.equalIgnoreWhiteSpace(expected.getName(), current.getName()));
         TestCase.assertEquals(expected.getName(), expected.getCharStart(), current.getCharStart());
         TestCase.assertEquals(expected.getName(), expected.getCharEnd(), current.getCharEnd());
         TestCase.assertEquals(expected.getName(), expected.getLineNumber(), current.getLineNumber());
         compareDebugElement(expected, current, true, compareVariables);
         if (expected.getThread() instanceof ISEDThread) {
            TestCase.assertTrue(current.getThread() instanceof ISEDThread);
            compareThread((ISEDThread)expected.getThread(), (ISEDThread)current.getThread(), false, compareVariables);
         }
         else {
            compareThread(expected.getThread(), current.getThread(), false, compareVariables);
         }
         // Compare variables
         if (compareVariables) {
            TestCase.assertEquals(expected.getName(), expected.hasVariables(), current.hasVariables());
            if (expected.hasVariables()) {
               IVariable[] expectedVariables = expected.getVariables();
               IVariable[] currentVariables = current.getVariables();
               compareVariables(expectedVariables, currentVariables, compareVariables);
            }
         }
      }
      else {
         TestCase.assertNull(current);
      }
   }
   
   /**
    * Compares the given {@link IVariable}s with each other. The order is not relevant.
    * @param expected The expected {@link IVariable}s.
    * @param current The current {@link IVariable}s.
    * @param compareVariables Compare variables?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareVariables(IVariable[] expected, IVariable[] current, boolean compareVariables) throws DebugException {
      TestCase.assertEquals(expected.length, current.length);
      // Compare ignore order
      List<IVariable> availableCurrentVariables = new LinkedList<IVariable>();
      CollectionUtil.addAll(availableCurrentVariables, current);
      for (int i = 0; i < expected.length; i++) {
         final IVariable expectedVariable = expected[i];
         // Find current variable with same name
         IVariable currentVariable = CollectionUtil.searchAndRemove(availableCurrentVariables, new IFilter<IVariable>() {
            @Override
            public boolean select(IVariable element) {
               try {
                  return element.getName().equalsIgnoreCase(expectedVariable.getName());
               }
               catch (DebugException e) {
                  throw new RuntimeException(e);
               }
            }
         });
         TestCase.assertNotNull(currentVariable);
         // Compare variables
         compareVariable(expectedVariable, currentVariable, compareVariables);
      }
      TestCase.assertTrue(availableCurrentVariables.isEmpty());
   }
   
   /**
    * Compares the given {@link IVariable}s with each other.
    * @param expected The expected {@link IVariable}.
    * @param current The current {@link IVariable}.
    * @param compareVariables Compare variables?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareVariable(IVariable expected, IVariable current, boolean compareVariables) throws DebugException {
      if (expected != null) {
         TestCase.assertNotNull(current);
         // Compare variable
         TestCase.assertTrue(expected.getName() + " does not match " + current.getName(), StringUtil.equalIgnoreWhiteSpace(expected.getName(), current.getName()));
         TestCase.assertEquals(expected.getName(), expected.getReferenceTypeName(), current.getReferenceTypeName());
         compareDebugElement(expected, current, true, compareVariables);
         // Compare value
         compareValue(expected.getValue(), current.getValue(), compareVariables);
      }
      else {
         TestCase.assertNull(current);
      }
   }

   /**
    * Compares the given {@link IValue}s with each other.
    * @param expected The expected {@link IValue}.
    * @param current The current {@link IValue}.
    * @param compareVariables Compare variables?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareValue(IValue expected, IValue current, boolean compareVariables) throws DebugException {
      if (expected != null) {
         TestCase.assertNotNull(current);
         // Compare value
         TestCase.assertEquals(expected.isAllocated(), current.isAllocated());
         TestCase.assertEquals(expected.getReferenceTypeName(), current.getReferenceTypeName());
         TestCase.assertTrue(expected.getValueString() + " does not match " + current.getValueString(), StringUtil.equalIgnoreWhiteSpace(expected.getValueString(), current.getValueString()));
         if (expected instanceof ISEDValue) {
            TestCase.assertTrue(current instanceof ISEDValue);
            TestCase.assertEquals(((ISEDValue)expected).isMultiValued(), ((ISEDValue)current).isMultiValued());
         }
         compareDebugElement(expected, current, true, compareVariables);
         // Compare variables
         TestCase.assertEquals(expected.hasVariables(), current.hasVariables());
         if (expected.hasVariables()) {
            IVariable[] expectedVariables = expected.getVariables();
            IVariable[] currentVariables = current.getVariables();
            compareVariables(expectedVariables, currentVariables, compareVariables);
         }
      }
      else {
         TestCase.assertNull(current);
      }
   }

   /**
    * Compares the given {@link IThread}s with each other.
    * @param expected The expected {@link IThread}.
    * @param current The current {@link IThread}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareVariables Compare variables?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareThread(IThread expected, IThread current, boolean compareReferences, boolean compareVariables) throws DebugException {
      // Compare thread
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.getName(), current.getName());
      TestCase.assertEquals(expected.getPriority(), current.getPriority());
      compareDebugElement(expected, current, compareReferences, compareVariables);
      if (compareReferences) {
         // Compare contained stack frames
         TestCase.assertEquals(expected.hasStackFrames(), current.hasStackFrames());
         IStackFrame[] expectedStackFrames = expected.getStackFrames();
         IStackFrame[] currentStackFrames = current.getStackFrames();
         TestCase.assertEquals(expectedStackFrames.length, currentStackFrames.length);
         for (int i = 0; i < expectedStackFrames.length; i++) {
            compareStackFrame(expectedStackFrames[i], currentStackFrames[i], compareVariables);
         }
         compareStackFrame(expected.getTopStackFrame(), current.getTopStackFrame(), compareVariables);
      }
   }
   
   /**
    * Compares the given {@link ISEDThread}s with each other.
    * @param expected The expected {@link ISEDThread}.
    * @param current The current {@link ISEDThread}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareThread(ISEDThread expected, 
                                       ISEDThread current, 
                                       boolean compareReferences, 
                                       boolean compareId, 
                                       boolean compareVariables,
                                       boolean compareCallStack) throws DebugException {
      compareThread((IThread)expected, (IThread)current, compareReferences, compareVariables);
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack);
   }

   /**
    * Compares the given {@link ISEDBranchCondition}s with each other.
    * @param expected The expected {@link ISEDBranchCondition}.
    * @param current The current {@link ISEDBranchCondition}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareBranchCondition(ISEDBranchCondition expected, 
                                                ISEDBranchCondition current, 
                                                boolean compareReferences, 
                                                boolean compareId, 
                                                boolean compareVariables,
                                                boolean compareCallStack) throws DebugException {
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack);
   }

   /**
    * Compares the given {@link ISEDBranchStatement}s with each other.
    * @param expected The expected {@link ISEDBranchStatement}.
    * @param current The current {@link ISEDBranchStatement}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareBranchStatement(ISEDBranchStatement expected, 
                                                ISEDBranchStatement current, 
                                                boolean compareReferences, 
                                                boolean compareId, 
                                                boolean compareVariables,
                                                boolean compareCallStack) throws DebugException {
      compareStackFrame(expected, current, compareVariables);
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack);
   }

   /**
    * Compares the given {@link ISEDMethodCall}s with each other.
    * @param expected The expected {@link ISEDMethodCall}.
    * @param current The current {@link ISEDMethodCall}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareMethodCall(ISEDMethodCall expected, 
                                           ISEDMethodCall current, 
                                           boolean compareReferences, 
                                           boolean compareId, 
                                           boolean compareVariables,
                                           boolean compareCallStack) throws DebugException {
      compareStackFrame(expected, current, compareVariables);
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack);
      compareMethodReturnConditions(expected.getMethodReturnConditions(), current.getMethodReturnConditions(), compareReferences, compareId, compareVariables, compareCallStack);
   }

   /**
    * Compares the given method return conditions.
    * @param expected The expected conditions.
    * @param current The current conditions.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareMethodReturnConditions(ISEDBranchCondition[] expected, 
                                                       ISEDBranchCondition[] current, 
                                                       boolean compareReferences, 
                                                       boolean compareId, 
                                                       boolean compareVariables, 
                                                       boolean compareCallStack) throws DebugException {
      if (expected != null) {
         assertNotNull(current);
         assertEquals(expected.length, current.length);
         for (int i = 0; i < expected.length; i++) {
            compareBranchCondition(expected[i], current[i], false, compareId, compareVariables, compareCallStack);
         }
      }
      else {
         assertNull(current);
      }
   }

   /**
    * Compares the given {@link ISEDLoopBodyTermination}s with each other.
    * @param expected The expected {@link ISEDLoopBodyTermination}.
    * @param current The current {@link ISEDLoopBodyTermination}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareLoopBodyTermination(ISEDLoopBodyTermination expected, 
                                                    ISEDLoopBodyTermination current, 
                                                    boolean compareReferences, 
                                                    boolean compareId, 
                                                    boolean compareVariables,
                                                    boolean compareCallStack) throws DebugException {
      compareTermination(expected, current, compareReferences, compareId, compareVariables, compareCallStack);
   }

   /**
    * Compares the given {@link ISEDExceptionalTermination}s with each other.
    * @param expected The expected {@link ISEDExceptionalTermination}.
    * @param current The current {@link ISEDExceptionalTermination}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareExceptionalTermination(ISEDExceptionalTermination expected, 
                                                       ISEDExceptionalTermination current, 
                                                       boolean compareReferences, 
                                                       boolean compareId, 
                                                       boolean compareVariables,
                                                       boolean compareCallStack) throws DebugException {
      compareTermination(expected, current, compareReferences, compareId, compareVariables, compareCallStack);
   }

   /**
    * Compares the given {@link ISEDLoopCondition}s with each other.
    * @param expected The expected {@link ISEDLoopCondition}.
    * @param current The current {@link ISEDLoopCondition}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareLoopCondition(ISEDLoopCondition expected, 
                                              ISEDLoopCondition current, 
                                              boolean compareReferences, 
                                              boolean compareId, 
                                              boolean compareVariables,
                                              boolean compareCallStack) throws DebugException {
      compareStackFrame(expected, current, compareVariables);
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack);
   }

   /**
    * Compares the given {@link ISEDLoopStatement}s with each other.
    * @param expected The expected {@link ISEDLoopStatement}.
    * @param current The current {@link ISEDLoopStatement}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareLoopStatement(ISEDLoopStatement expected, 
                                              ISEDLoopStatement current, 
                                              boolean compareReferences, 
                                              boolean compareId, 
                                              boolean compareVariables,
                                              boolean compareCallStack) throws DebugException {
      compareStackFrame(expected, current, compareVariables);
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack);
   }

   /**
    * Compares the given {@link ISEDMethodReturn}s with each other.
    * @param expected The expected {@link ISEDMethodReturn}.
    * @param current The current {@link ISEDMethodReturn}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareMethodReturn(ISEDMethodReturn expected, 
                                             ISEDMethodReturn current, 
                                             boolean compareReferences, 
                                             boolean compareId, 
                                             boolean compareVariables,
                                             boolean compareCallStack) throws DebugException {
      compareStackFrame(expected, current, compareVariables);
      compareNode(expected.getMethodReturnCondition(), current.getMethodReturnCondition(), false, compareId, compareVariables, compareCallStack);
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack);
   }

   /**
    * Compares the given {@link ISEDStatement}s with each other.
    * @param expected The expected {@link ISEDStatement}.
    * @param current The current {@link ISEDStatement}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareStatement(ISEDStatement expected, 
                                          ISEDStatement current, 
                                          boolean compareReferences, 
                                          boolean compareId, 
                                          boolean compareVariables,
                                          boolean compareCallStack) throws DebugException {
      compareStackFrame(expected, current, compareVariables);
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack);
   }

   /**
    * Compares the given {@link ISEDMethodContract}s with each other.
    * @param expected The expected {@link ISEDMethodContract}.
    * @param current The current {@link ISEDMethodContract}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareMethodContract(ISEDMethodContract expected, 
                                                  ISEDMethodContract current, 
                                                  boolean compareReferences, 
                                                  boolean compareId, 
                                                  boolean compareVariables,
                                                  boolean compareCallStack) throws DebugException {
      compareStackFrame(expected, current, compareVariables);
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack);
      assertEquals(expected.isPreconditionComplied(), current.isPreconditionComplied());
      assertEquals(expected.hasNotNullCheck(), current.hasNotNullCheck());
      assertEquals(expected.isNotNullCheckComplied(), current.isNotNullCheckComplied());
   }

   /**
    * Compares the given {@link ISEDLoopInvariant}s with each other.
    * @param expected The expected {@link ISEDLoopInvariant}.
    * @param current The current {@link ISEDLoopInvariant}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareLoopInvariant(ISEDLoopInvariant expected, 
                                              ISEDLoopInvariant current, 
                                              boolean compareReferences, 
                                              boolean compareId, 
                                              boolean compareVariables,
                                              boolean compareCallStack) throws DebugException {
      compareStackFrame(expected, current, compareVariables);
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack);
      assertEquals(expected.isInitiallyValid(), current.isInitiallyValid());
   }

   /**
    * Compares the given {@link ISEDTermination}s with each other.
    * @param expected The expected {@link ISEDTermination}.
    * @param current The current {@link ISEDTermination}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareTermination(ISEDTermination expected, 
                                            ISEDTermination current, 
                                            boolean compareReferences, 
                                            boolean compareId, 
                                            boolean compareVariables,
                                            boolean compareCallStack) throws DebugException {
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack);
      assertEquals(expected.isVerified(), current.isVerified());
   }
   
   /**
    * Waits until the user interface is ready.
    */
   public static void waitForDebugTreeInterface() {
      TestUtilsUtil.sleep(100);
      TestUtilsUtil.waitForJobs();
   }
   
   /**
    * Method to select an item in the debug tree.
    * @param debugTree The debug tree.
    * @param indexPathToItem The indices on parents to select.
    * @return The selected {@link SWTBotTreeItem}.
    */
   public static SWTBotTreeItem selectInDebugTree(SWTBotTree debugTree, int... indexPathToItem) {
      TestCase.assertNotNull(indexPathToItem);
      TestCase.assertTrue(indexPathToItem.length >= 1);
      SWTBotTreeItem item = null;
      for (int i = 1; i < indexPathToItem.length + 1; i++) {
         int[] subPath = Arrays.copyOf(indexPathToItem, i);
         item = TestUtilsUtil.selectInTree(debugTree, subPath);
         if (!item.isExpanded()) {
            item.expand();
         }
         TestUtilsUtil.waitForJobs();
      }
      return item;
   }
}