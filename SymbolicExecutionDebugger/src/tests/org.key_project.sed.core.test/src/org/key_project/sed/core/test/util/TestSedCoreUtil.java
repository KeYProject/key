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
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

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
import org.eclipse.debug.core.model.ITerminate;
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
import org.eclipse.debug.ui.IDebugView;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.viewers.ILazyTreePathContentProvider;
import org.eclipse.jface.viewers.TreeViewer;
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
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.model.ISEBaseMethodReturn;
import org.key_project.sed.core.model.ISEBranchCondition;
import org.key_project.sed.core.model.ISEBranchStatement;
import org.key_project.sed.core.model.ISEConstraint;
import org.key_project.sed.core.model.ISEDebugElement;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISEExceptionalMethodReturn;
import org.key_project.sed.core.model.ISEExceptionalTermination;
import org.key_project.sed.core.model.ISEGroupable;
import org.key_project.sed.core.model.ISELoopBodyTermination;
import org.key_project.sed.core.model.ISELoopCondition;
import org.key_project.sed.core.model.ISELoopInvariant;
import org.key_project.sed.core.model.ISELoopStatement;
import org.key_project.sed.core.model.ISEMethodCall;
import org.key_project.sed.core.model.ISEMethodContract;
import org.key_project.sed.core.model.ISEMethodReturn;
import org.key_project.sed.core.model.ISEStatement;
import org.key_project.sed.core.model.ISETermination;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.model.ISEValue;
import org.key_project.sed.core.util.ISEIterator;
import org.key_project.sed.core.util.LaunchUtil;
import org.key_project.sed.core.util.SEDPreferenceUtil;
import org.key_project.sed.core.util.SEPreorderIterator;
import org.key_project.sed.ui.perspective.SymbolicDebugPerspectiveFactory;
import org.key_project.sed.ui.util.SEDUIUtil;
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
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(targetItems[0]) instanceof ISEDebugTarget);
      // Assert thread
      SWTBotTreeItem[] threadItems = targetItems[0].getItems();
      TestCase.assertEquals(1, threadItems.length);
      TestCase.assertEquals("Fixed Example Thread", threadItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(threadItems[0]) instanceof ISEThread);
      // Assert statement1
      SWTBotTreeItem[] statement1Items = threadItems[0].getItems();
      TestCase.assertEquals(1, statement1Items.length);
      TestCase.assertEquals("int x = 1;", statement1Items[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statement1Items[0]) instanceof ISEStatement);
      // Assert loop statement
      SWTBotTreeItem[] loopNodeItems = statement1Items[0].getItems();
      TestCase.assertEquals(1, loopNodeItems.length);
      TestCase.assertEquals("while (x == 1)", loopNodeItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(loopNodeItems[0]) instanceof ISELoopStatement);
      // Assert loop condition
      SWTBotTreeItem[] loopConditionItems = loopNodeItems[0].getItems();
      TestCase.assertEquals(1, loopConditionItems.length);
      TestCase.assertEquals("x == 1", loopConditionItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(loopConditionItems[0]) instanceof ISELoopCondition);
      // Assert loop statement
      SWTBotTreeItem[] loopStatementItems = loopConditionItems[0].getItems();
      TestCase.assertEquals(1, loopStatementItems.length);
      TestCase.assertEquals("x++;", loopStatementItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(loopStatementItems[0]) instanceof ISEStatement);
      // Assert statement2
      SWTBotTreeItem[] statement2Items = loopStatementItems[0].getItems();
      TestCase.assertEquals(1, statement2Items.length);
      TestCase.assertEquals("int y = 2;", statement2Items[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statement2Items[0]) instanceof ISEStatement);
      // Assert statement3
      SWTBotTreeItem[] statement3Items = statement2Items[0].getItems();
      TestCase.assertEquals(1, statement3Items.length);
      TestCase.assertEquals("int result = (x + y) / z;", statement3Items[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statement3Items[0]) instanceof ISEStatement);
      // Assert branch conditions
      SWTBotTreeItem[] conditions1Items = statement3Items[0].getItems();
      TestCase.assertEquals(2, conditions1Items.length);
      TestCase.assertEquals("z == 0", conditions1Items[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(conditions1Items[0]) instanceof ISEBranchCondition);
      TestCase.assertEquals("z != 0", conditions1Items[1].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(conditions1Items[1]) instanceof ISEBranchCondition);
      // Assert branch zero
      SWTBotTreeItem[] branchZeroItems = conditions1Items[0].getItems();
      TestCase.assertEquals(1, branchZeroItems.length);
      TestCase.assertEquals("throws DivisionByZeroException()", branchZeroItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(branchZeroItems[0]) instanceof ISEExceptionalTermination);
      // Assert branch not zero
      SWTBotTreeItem[] branchNotZeroItems = conditions1Items[1].getItems();
      TestCase.assertEquals(1, branchNotZeroItems.length);
      TestCase.assertEquals("foo(result)", branchNotZeroItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(branchNotZeroItems[0]) instanceof ISEMethodCall);
      // Assert method call
      SWTBotTreeItem[] callItems = branchNotZeroItems[0].getItems();
      TestCase.assertEquals(1, callItems.length);
      TestCase.assertEquals("if (result >= 0)", callItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(callItems[0]) instanceof ISEBranchStatement);
      // Assert branch conditions
      SWTBotTreeItem[] conditions2Items = callItems[0].getItems();
      TestCase.assertEquals(2, conditions2Items.length);
      TestCase.assertEquals("result < 0", conditions2Items[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(conditions2Items[0]) instanceof ISEBranchCondition);
      TestCase.assertEquals("result >= 0", conditions2Items[1].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(conditions2Items[1]) instanceof ISEBranchCondition);
      // Assert branch negative
      SWTBotTreeItem[] negativeItems = conditions2Items[0].getItems();
      TestCase.assertEquals(1, negativeItems.length);
      TestCase.assertEquals("return -1", negativeItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(negativeItems[0]) instanceof ISEMethodReturn);
      // Assert termination negative
      SWTBotTreeItem[] negativeTerminationItems = negativeItems[0].getItems();
      TestCase.assertEquals(1, negativeTerminationItems.length);
      TestCase.assertEquals("<end>", negativeTerminationItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(negativeTerminationItems[0]) instanceof ISETermination);
      // Assert termination negative empty
      SWTBotTreeItem[] negativeTerminationEmptyItems = negativeTerminationItems[0].getItems();
      TestCase.assertEquals(0, negativeTerminationEmptyItems.length);
      // Assert branch positive
      SWTBotTreeItem[] positiveItems = conditions2Items[1].getItems();
      TestCase.assertEquals(1, positiveItems.length);
      TestCase.assertEquals("return 1", positiveItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(positiveItems[0]) instanceof ISEExceptionalMethodReturn);
      // Assert termination positive
      SWTBotTreeItem[] positiveTerminationItems = positiveItems[0].getItems();
      TestCase.assertEquals(1, positiveTerminationItems.length);
      TestCase.assertEquals("<loop body end>", positiveTerminationItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(positiveTerminationItems[0]) instanceof ISETermination);
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
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(targetItems[0]) instanceof ISEDebugTarget);
      // Assert thread
      SWTBotTreeItem[] threadItems = targetItems[0].getItems();
      TestCase.assertEquals(1, threadItems.length);
      TestCase.assertEquals("Fixed Example Thread", threadItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(threadItems[0]) instanceof ISEThread);
      // Assert statement1, loop statement, loop condition, loop statement, statement 2 and 3
      SWTBotTreeItem[] statementItems = threadItems[0].getItems();
      TestCase.assertEquals(6, statementItems.length);
      TestCase.assertEquals("int x = 1;", statementItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statementItems[0]) instanceof ISEStatement);
      TestCase.assertEquals(0, statementItems[0].getItems().length);

      TestCase.assertEquals("while (x == 1)", statementItems[1].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statementItems[1]) instanceof ISELoopStatement);
      TestCase.assertEquals(0, statementItems[1].getItems().length);
      TestCase.assertEquals("x == 1", statementItems[2].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statementItems[2]) instanceof ISELoopCondition);
      TestCase.assertEquals(0, statementItems[2].getItems().length);
      TestCase.assertEquals("x++;", statementItems[3].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statementItems[3]) instanceof ISEStatement);
      TestCase.assertEquals(0, statementItems[3].getItems().length);
      
      TestCase.assertEquals("int y = 2;", statementItems[4].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statementItems[4]) instanceof ISEStatement);
      TestCase.assertEquals(0, statementItems[4].getItems().length);
      TestCase.assertEquals("int result = (x + y) / z;", statementItems[5].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statementItems[5]) instanceof ISEStatement);
      // Assert branch conditions
      SWTBotTreeItem[] conditions1Items = statementItems[5].getItems();
      TestCase.assertEquals(2, conditions1Items.length);
      TestCase.assertEquals("z == 0", conditions1Items[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(conditions1Items[0]) instanceof ISEBranchCondition);
      TestCase.assertEquals("z != 0", conditions1Items[1].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(conditions1Items[1]) instanceof ISEBranchCondition);
      // Assert branch zero
      SWTBotTreeItem[] branchZeroItems = conditions1Items[0].getItems();
      TestCase.assertEquals(1, branchZeroItems.length);
      TestCase.assertEquals("throws DivisionByZeroException()", branchZeroItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(branchZeroItems[0]) instanceof ISEExceptionalTermination);
      // Assert branch not zero
      SWTBotTreeItem[] branchNotZeroItems = conditions1Items[1].getItems();
      TestCase.assertEquals(2, branchNotZeroItems.length);
      TestCase.assertEquals("foo(result)", branchNotZeroItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(branchNotZeroItems[0]) instanceof ISEMethodCall);
      TestCase.assertEquals(0, branchNotZeroItems[0].getItems().length);
      TestCase.assertEquals("if (result >= 0)", branchNotZeroItems[1].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(branchNotZeroItems[1]) instanceof ISEBranchStatement);
      // Assert branch conditions
      SWTBotTreeItem[] conditions2Items = branchNotZeroItems[1].getItems();
      TestCase.assertEquals(2, conditions2Items.length);
      TestCase.assertEquals("result < 0", conditions2Items[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(conditions2Items[0]) instanceof ISEBranchCondition);
      TestCase.assertEquals("result >= 0", conditions2Items[1].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(conditions2Items[1]) instanceof ISEBranchCondition);
      // Assert branch negative
      SWTBotTreeItem[] negativeItems = conditions2Items[0].getItems();
      TestCase.assertEquals(2, negativeItems.length);
      TestCase.assertEquals("return -1", negativeItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(negativeItems[0]) instanceof ISEMethodReturn);
      TestCase.assertEquals(0, negativeItems[0].getItems().length);
      TestCase.assertEquals("<end>", negativeItems[1].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(negativeItems[1]) instanceof ISETermination);
      TestCase.assertEquals(0, negativeItems[1].getItems().length);
      // Assert branch positive
      SWTBotTreeItem[] positiveItems = conditions2Items[1].getItems();
      TestCase.assertEquals(2, positiveItems.length);
      TestCase.assertEquals("return 1", positiveItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(positiveItems[0]) instanceof ISEExceptionalMethodReturn);
      TestCase.assertEquals(0, positiveItems[0].getItems().length);
      TestCase.assertEquals("<loop body end>", positiveItems[1].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(positiveItems[1]) instanceof ISETermination);
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
            boolean terminated = false;
            Object data = TestUtilsUtil.getTreeItemData(item);
            if (data instanceof ITerminate) {
               terminated = ((ITerminate)data).isTerminated();
            }
            item.select();
            item.contextMenu("Terminate and Remove").click();
            try{
               if (!terminated) {
                  SWTBotShell dialog = bot.shell("Terminate and Remove");
                  dialog.bot().button("Yes").click();
               }
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
    * Waits until the given {@link SWTBotTree} contains at least one {@link ISEDebugTarget}.
    * @param bot The {@link SWTBot} to use.
    * @param debugTree The {@link SWTBotTree} to search in.
    * @return The first found {@link ISEDebugTarget}.
    */
   public static ISEDebugTarget waitUntilDebugTreeHasDebugTarget(SWTBot bot, final SWTBotTree debugTree) {
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
       * The found {@link ISEDebugTarget}.
       */
      private ISEDebugTarget target; 
      
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
                     if (data instanceof ISEDebugTarget) {
                        target = (ISEDebugTarget)data;
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
       * Returns the found {@link ISEDebugTarget}.
       * @return The found {@link ISEDebugTarget}.
       */
      public ISEDebugTarget getTarget() {
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
            return launch.isTerminated() && !launch.canTerminate();
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
    * @param target The {@link ISEDebugTarget} to wait for.
    */
   public static void waitUntilDebugTargetCanSuspend(SWTBot bot, final ISEDebugTarget target) {
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
    * @param target The {@link ISEDebugTarget} to wait for.
    */
   public static void waitUntilDebugTargetCanResume(SWTBot bot, final ISEDebugTarget target) {
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
    * Suspends the given {@link ISEDebugTarget} as soon as possible.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param target The {@link ISEDebugTarget} to suspend.
    */
   public static void suspend(SWTWorkbenchBot bot, final ISEDebugTarget target) {
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
    * Compares the given {@link ISEDebugTarget}s with each other.
    * @param expected The expected {@link ISEDebugTarget}.
    * @param current The current {@link ISEDebugTarget}.
    * @param compareId Compare the value of {@link ISEDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   public static void compareDebugTarget(ISEDebugTarget expected, 
                                         ISEDebugTarget current, 
                                         boolean compareId, 
                                         boolean compareVariables,
                                         boolean compareCallStack,
                                         boolean compareConstraints) throws DebugException {
      // Compare annotations
      ISEAnnotation[] expectedAnnotations = expected.getRegisteredAnnotations();
      ISEAnnotation[] currentAnnotations = current.getRegisteredAnnotations();
      assertEquals(expectedAnnotations.length, currentAnnotations.length);
      for (int i = 0; i < expectedAnnotations.length; i++) {
         compareAnnotation(expectedAnnotations[i], currentAnnotations[i]);
      }
      // Compare nodes
      ISEIterator expectedIter = new SEPreorderIterator(expected);
      ISEIterator currentIter = new SEPreorderIterator(current);
      while (expectedIter.hasNext()) {
         TestCase.assertTrue(currentIter.hasNext());
         ISEDebugElement expectedNext = expectedIter.next();
         ISEDebugElement currentNext = currentIter.next();
         if (expectedNext instanceof ISEDebugTarget) {
            TestCase.assertTrue("Expected ISEDDebugTarget on " + ((ISEDebugTarget)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEDebugTarget);
            compareDebugElement(expectedNext, currentNext, true, compareId, compareConstraints);
            compareDebugTarget((IDebugTarget)expectedNext, (IDebugTarget)currentNext, true, compareVariables, compareConstraints);
         }
         else if (expectedNext instanceof ISEBranchCondition) {
            TestCase.assertTrue("Expected ISEDBranchCondition on " + ((ISEBranchCondition)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEBranchCondition);
            compareBranchCondition((ISEBranchCondition)expectedNext, (ISEBranchCondition)currentNext, true, compareId, compareVariables, compareCallStack, compareConstraints);
         }
         else if (expectedNext instanceof ISEBranchStatement) {
            TestCase.assertTrue("Expected ISEDBranchStatement on " + ((ISEBranchStatement)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEBranchStatement);
            compareBranchStatement((ISEBranchStatement)expectedNext, (ISEBranchStatement)currentNext, true, compareId, compareVariables, compareCallStack, compareConstraints);
         }
         else if (expectedNext instanceof ISEExceptionalTermination) {
            TestCase.assertTrue("Expected ISEDExceptionalTermination on " + ((ISEExceptionalTermination)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEExceptionalTermination);
            compareExceptionalTermination((ISEExceptionalTermination)expectedNext, (ISEExceptionalTermination)currentNext, true, compareId, compareVariables, compareCallStack, compareConstraints);
         }
         else if (expectedNext instanceof ISELoopCondition) {
            TestCase.assertTrue("Expected ISEDLoopCondition on " + ((ISELoopCondition)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISELoopCondition);
            compareLoopCondition((ISELoopCondition)expectedNext, (ISELoopCondition)currentNext, true, compareId, compareVariables, compareCallStack, compareConstraints);
         }
         else if (expectedNext instanceof ISELoopStatement) {
            TestCase.assertTrue("Expected ISEDLoopStatement on " + ((ISELoopStatement)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISELoopStatement);
            compareLoopStatement((ISELoopStatement)expectedNext, (ISELoopStatement)currentNext, true, compareId, compareVariables, compareCallStack, compareConstraints);
         }
         else if (expectedNext instanceof ISEMethodCall) {
            TestCase.assertTrue("Expected ISEDMethodCall on " + ((ISEMethodCall)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEMethodCall);
            compareMethodCall((ISEMethodCall)expectedNext, (ISEMethodCall)currentNext, true, compareId, compareVariables, compareCallStack, compareConstraints);
         }
         else if (expectedNext instanceof ISEMethodReturn) {
            TestCase.assertTrue("Expected ISEDMethodReturn on " + ((ISEMethodReturn)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEMethodReturn);
            compareMethodReturn((ISEMethodReturn)expectedNext, (ISEMethodReturn)currentNext, true, compareId, compareVariables, compareCallStack, compareConstraints);
         }
         else if (expectedNext instanceof ISEExceptionalMethodReturn) {
            TestCase.assertTrue("Expected ISEDExceptionalMethodReturn on " + ((ISEExceptionalMethodReturn)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEExceptionalMethodReturn);
            compareExceptionalMethodReturn((ISEExceptionalMethodReturn)expectedNext, (ISEExceptionalMethodReturn)currentNext, true, compareId, compareVariables, compareCallStack, compareConstraints);
         }
         else if (expectedNext instanceof ISEStatement) {
            TestCase.assertTrue("Expected ISEDStatement on " + ((ISEStatement)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEStatement);
            compareStatement((ISEStatement)expectedNext, (ISEStatement)currentNext, true, compareId, compareVariables, compareCallStack, compareConstraints);
         }
         else if (expectedNext instanceof ISETermination) {
            TestCase.assertTrue("Expected ISEDTermination on " + ((ISETermination)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISETermination);
            compareTermination((ISETermination)expectedNext, (ISETermination)currentNext, true, compareId, compareVariables, compareCallStack, compareConstraints);
         }
         else if (expectedNext instanceof ISEThread) {
            TestCase.assertTrue("Expected ISEDThread on " + ((ISEThread)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEThread);
            compareThread((ISEThread)expectedNext, (ISEThread)currentNext, true, compareId, compareVariables, compareCallStack, compareConstraints);
         }
         else if (expectedNext instanceof ISEMethodContract) {
            TestCase.assertTrue("Expected ISEDMethodContract on " + ((ISEMethodContract)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISEMethodContract);
            compareMethodContract((ISEMethodContract)expectedNext, (ISEMethodContract)currentNext, true, compareId, compareVariables, compareCallStack, compareConstraints);
         }
         else if (expectedNext instanceof ISELoopInvariant) {
            TestCase.assertTrue("Expected ISEDLoopInvariant on " + ((ISELoopInvariant)expectedNext).getName() + " instance but is " + ObjectUtil.getClass(currentNext) + ".", currentNext instanceof ISELoopInvariant);
            compareLoopInvariant((ISELoopInvariant)expectedNext, (ISELoopInvariant)currentNext, true, compareId, compareVariables, compareCallStack, compareConstraints);
         }
         else {
            TestCase.fail("Unknown node type \"" + (expectedNext != null ? expectedNext.getClass() : null) + "\".");
         }
      }
      TestCase.assertFalse(expectedIter.hasNext());
      TestCase.assertFalse(currentIter.hasNext());
   }
   
   /**
    * Compares the given {@link ISEAnnotation}s with each other.
    * @param expected The expected {@link ISEAnnotation}.
    * @param current The current {@link ISEAnnotation}.
    */
   protected static void compareAnnotation(ISEAnnotation expected, ISEAnnotation current) {
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
    * Compares the given {@link ISEAnnotationLink}s with each other.
    * @param expected The expected {@link ISEAnnotationLink}.
    * @param current The current {@link ISEAnnotationLink}.
    */
   protected static void compareAnnotationLink(ISEAnnotationLink expected, ISEAnnotationLink current) {
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
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareDebugTarget(IDebugTarget expected, 
                                            IDebugTarget current, 
                                            boolean compareReferences, 
                                            boolean compareVariables,
                                            boolean compareConstraints) throws DebugException {
      // Compare debug target
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.getName(), current.getName());
      compareDebugElement(expected, current, false, compareVariables, compareConstraints);
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
            compareThread(expectedThreads[i], currentThreads[i], false, compareVariables, compareConstraints);
         }
      }
   }
   
   /**
    * Compares the given {@link ISENode}s with each other.
    * @param expected The expected {@link ISENode}.
    * @param current The current {@link ISENode}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareNode(ISENode expected, 
                                     ISENode current, 
                                     boolean compareReferences, 
                                     boolean compareId, 
                                     boolean compareVariables,
                                     boolean compareCallStack,
                                     boolean compareConstraints) throws DebugException {
      if (expected != null) {
         // Compare node
         TestCase.assertNotNull(current);
         TestCase.assertTrue(expected.getName() + " does not match " + current.getName(), StringUtil.equalIgnoreWhiteSpace(expected.getName(), current.getName()));
         TestCase.assertTrue(expected.getPathCondition() + " does not match " + current.getPathCondition(), StringUtil.equalIgnoreWhiteSpace(expected.getPathCondition(), current.getPathCondition()));
         TestCase.assertEquals(expected.getNodeType(), current.getNodeType());
         compareDebugElement(expected, current, compareReferences, compareVariables, compareConstraints);
         // Compare annotation links
         ISEAnnotationLink[] expectedAnnotationLinks = expected.getAnnotationLinks();
         ISEAnnotationLink[] currentAnnotationLinks = current.getAnnotationLinks();
         assertEquals(expectedAnnotationLinks.length, currentAnnotationLinks.length);
         for (int i = 0; i < expectedAnnotationLinks.length; i++) {
            compareAnnotationLink(expectedAnnotationLinks[i], currentAnnotationLinks[i]);
         }
         // Compare call stack
         if (compareCallStack) {
            compareCallStack(expected.getCallStack(), current.getCallStack());
         }
         // Constraints
         if (compareConstraints) {
            compareConstraints(expected.getConstraints(), current.getConstraints(), compareVariables, compareConstraints);
         }
         // Compare group starts
         compareConditions(expected.getGroupStartConditions(), current.getGroupStartConditions(), compareReferences, compareId, compareVariables, compareCallStack, compareConstraints);
         // Compare group ends
         if (expected instanceof ISEGroupable) {
            assertTrue(current instanceof ISEGroupable);
            assertEquals(((ISEGroupable) expected).isGroupable(), ((ISEGroupable) current).isGroupable());
            compareConditions(((ISEGroupable) expected).getGroupEndConditions(), ((ISEGroupable) current).getGroupEndConditions(), compareReferences, compareId, compareVariables, compareCallStack, compareConstraints);
         }
         else {
            assertFalse(current instanceof ISEGroupable);
         }
         // Compare call states
         if (expected instanceof ISEBaseMethodReturn) {
            assertTrue(current instanceof ISEBaseMethodReturn);
            if (compareVariables) {
               compareVariables(((ISEBaseMethodReturn) expected).getCallStateVariables(), ((ISEBaseMethodReturn) current).getCallStateVariables(), compareVariables, compareConstraints);
            }
         }
         else {
            assertFalse(current instanceof ISEBaseMethodReturn);
         }
         // Compare parent
         if (compareReferences) {
            compareNode(expected.getParent(), current.getParent(), false, compareId, compareVariables, compareCallStack, compareConstraints);
            // Compare children
            ISENode[] expectedChildren = expected.getChildren();
            ISENode[] currentChildren = current.getChildren();
            TestCase.assertEquals("Number of children of " + expected + " is not equal to number of children of " + current + ".", expectedChildren.length, currentChildren.length);
            for (int i = 0; i < expectedChildren.length; i++) {
               if (expectedChildren[i] instanceof ISEBranchCondition) {
                  TestCase.assertTrue("Expected ISEDBranchCondition on " + ((ISEBranchCondition)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEBranchCondition);
                  compareBranchCondition((ISEBranchCondition)expectedChildren[i], (ISEBranchCondition)currentChildren[i], false, compareId, compareVariables, compareCallStack, compareConstraints);
               }
               else if (expectedChildren[i] instanceof ISEBranchStatement) {
                  TestCase.assertTrue("Expected ISEDBranchStatement on " + ((ISEBranchStatement)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEBranchStatement);
                  compareBranchStatement((ISEBranchStatement)expectedChildren[i], (ISEBranchStatement)currentChildren[i], false, compareId, compareVariables, compareCallStack, compareConstraints);
               }
               else if (expectedChildren[i] instanceof ISEExceptionalTermination) {
                  TestCase.assertTrue("Expected ISEDExceptionalTermination on " + ((ISEExceptionalTermination)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEExceptionalTermination);
                  compareExceptionalTermination((ISEExceptionalTermination)expectedChildren[i], (ISEExceptionalTermination)currentChildren[i], false, compareId, compareVariables, compareCallStack, compareConstraints);
               }
               else if (expectedChildren[i] instanceof ISELoopBodyTermination) {
                  TestCase.assertTrue("Expected ISEDLoopBodyTermination on " + ((ISELoopBodyTermination)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISELoopBodyTermination);
                  compareLoopBodyTermination((ISELoopBodyTermination)expectedChildren[i], (ISELoopBodyTermination)currentChildren[i], false, compareId, compareVariables, compareCallStack, compareConstraints);
               }
               else if (expectedChildren[i] instanceof ISELoopCondition) {
                  TestCase.assertTrue("Expected ISEDLoopCondition on " + ((ISELoopCondition)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISELoopCondition);
                  compareLoopCondition((ISELoopCondition)expectedChildren[i], (ISELoopCondition)currentChildren[i], false, compareId, compareVariables, compareCallStack, compareConstraints);
               }
               else if (expectedChildren[i] instanceof ISELoopStatement) {
                  TestCase.assertTrue("Expected ISEDLoopStatement on " + ((ISELoopStatement)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISELoopStatement);
                  compareLoopStatement((ISELoopStatement)expectedChildren[i], (ISELoopStatement)currentChildren[i], false, compareId, compareVariables, compareCallStack, compareConstraints);
               }
               else if (expectedChildren[i] instanceof ISELoopCondition) {
                  TestCase.assertTrue("Expected ISEDLoopCondition on " + ((ISELoopCondition)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISELoopCondition);
                  compareLoopCondition((ISELoopCondition)expectedChildren[i], (ISELoopCondition)currentChildren[i], false, compareId, compareVariables, compareCallStack, compareConstraints);
               }
               else if (expectedChildren[i] instanceof ISELoopStatement) {
                  TestCase.assertTrue("Expected ISEDLoopStatement on " + ((ISELoopStatement)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISELoopStatement);
                  compareLoopStatement((ISELoopStatement)expectedChildren[i], (ISELoopStatement)currentChildren[i], false, compareId, compareVariables, compareCallStack, compareConstraints);
               }
               else if (expectedChildren[i] instanceof ISEMethodCall) {
                  TestCase.assertTrue("Expected ISEDMethodCall on " + ((ISEMethodCall)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEMethodCall);
                  compareMethodCall((ISEMethodCall)expectedChildren[i], (ISEMethodCall)currentChildren[i], false, compareId, compareVariables, compareCallStack, compareConstraints);
               }
               else if (expectedChildren[i] instanceof ISEMethodReturn) {
                  TestCase.assertTrue("Expected ISEDMethodReturn on " + ((ISEMethodReturn)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEMethodReturn);
                  compareMethodReturn((ISEMethodReturn)expectedChildren[i], (ISEMethodReturn)currentChildren[i], false, compareId, compareVariables, compareCallStack, compareConstraints);
               }
               else if (expectedChildren[i] instanceof ISEExceptionalMethodReturn) {
                  TestCase.assertTrue("Expected ISEDExceptionalMethodReturn on " + ((ISEExceptionalMethodReturn)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEExceptionalMethodReturn);
                  compareExceptionalMethodReturn((ISEExceptionalMethodReturn)expectedChildren[i], (ISEExceptionalMethodReturn)currentChildren[i], false, compareId, compareVariables, compareCallStack, compareConstraints);
               }
               else if (expectedChildren[i] instanceof ISEStatement) {
                  TestCase.assertTrue("Expected ISEDStatement on " + ((ISEStatement)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEStatement);
                  compareStatement((ISEStatement)expectedChildren[i], (ISEStatement)currentChildren[i], false, compareId, compareVariables, compareCallStack, compareConstraints);
               }
               else if (expectedChildren[i] instanceof ISETermination) {
                  TestCase.assertTrue("Expected ISEDTermination on " + ((ISETermination)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISETermination);
                  compareTermination((ISETermination)expectedChildren[i], (ISETermination)currentChildren[i], false, compareId, compareVariables, compareCallStack, compareConstraints);
               }
               else if (expectedChildren[i] instanceof ISEThread) {
                  TestCase.assertTrue("Expected ISEDThread on " + ((ISEThread)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEThread);
                  compareThread((ISEThread)expectedChildren[i], (ISEThread)currentChildren[i], true, compareVariables, compareConstraints);
               }
               else if (expectedChildren[i] instanceof ISEMethodContract) {
                  TestCase.assertTrue("Expected ISEDMethodContract on " + ((ISEMethodContract)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISEMethodContract);
                  compareMethodContract((ISEMethodContract)expectedChildren[i], (ISEMethodContract)currentChildren[i], false, compareId, compareVariables, compareCallStack, compareConstraints);
               }
               else if (expectedChildren[i] instanceof ISELoopInvariant) {
                  TestCase.assertTrue("Expected ISEDLoopInvariant on " + ((ISELoopInvariant)expectedChildren[i]).getName() + " instance but is " + ObjectUtil.getClass(currentChildren[i]) + ".", currentChildren[i] instanceof ISELoopInvariant);
                  compareLoopInvariant((ISELoopInvariant)expectedChildren[i], (ISELoopInvariant)currentChildren[i], false, compareId, compareVariables, compareCallStack, compareConstraints);
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
    * @param expected The expected {@link ISENode}s.
    * @param current The current {@link ISENode}s.
    * @throws DebugException Occurred Exception.
    */
   protected static void compareCallStack(ISENode[] expectedEntries, 
                                          ISENode[] currentEntries) throws DebugException {
      if (expectedEntries != null) {
         TestCase.assertNotNull(currentEntries);
         TestCase.assertEquals(expectedEntries.length, currentEntries.length);
         for (int i = 0; i < expectedEntries.length; i++) {
            compareNode(expectedEntries[i], currentEntries[i], false, false, false, false, false);
         }
      }
      else {
         TestCase.assertTrue(ArrayUtil.isEmpty(currentEntries));
      }
   }
   
   /**
    * Compares the given termination entries.
    * @param expected The expected {@link ISETermination}s.
    * @param current The current {@link ISETermination}s.
    * @throws DebugException Occurred Exception.
    */
   protected static void compareTerminations(ISETermination[] expectedEntries, 
                                             ISETermination[] currentEntries) throws DebugException {
      if (expectedEntries != null) {
         TestCase.assertNotNull(currentEntries);
         TestCase.assertEquals(expectedEntries.length, currentEntries.length);
         for (int i = 0; i < expectedEntries.length; i++) {
            compareNode(expectedEntries[i], currentEntries[i], false, false, false, false, false);
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
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareDebugElement(IDebugElement expected, IDebugElement current, boolean compareReferences, boolean compareVariables, boolean compareConstraints) throws DebugException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.getModelIdentifier(), current.getModelIdentifier());
      if (compareReferences) {
         if (expected.getDebugTarget() instanceof ISEDebugTarget) {
            TestCase.assertTrue(current.getDebugTarget() instanceof ISEDebugTarget);
            compareDebugTarget((IDebugTarget)expected.getDebugTarget(), (IDebugTarget)current.getDebugTarget(), false, compareVariables, compareConstraints);
         }
         else {
            compareDebugTarget(expected.getDebugTarget(), current.getDebugTarget(), false, compareVariables, compareConstraints);
         }
      }
   }
   
   /**
    * Compares the given {@link IDebugElement}s with each other.
    * @param expected The expected {@link IDebugElement}.
    * @param current The current {@link IDebugElement}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareDebugElement(ISEDebugElement expected, ISEDebugElement current, boolean compareReferences, boolean compareId, boolean compareVariables, boolean compareConstraints) throws DebugException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      if (compareId) {
         TestCase.assertEquals(expected.getId(), current.getId());
      }
      compareDebugElement((IDebugElement)expected, (IDebugElement)current, compareReferences, compareVariables, compareConstraints);
   }
   
   /**
    * Compares the given {@link IStackFrame}s with each other.
    * @param expected The expected {@link IStackFrame}.
    * @param current The current {@link IStackFrame}.
    * @param compareVariables Compare variables?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareStackFrame(IStackFrame expected, IStackFrame current, boolean compareVariables, boolean compareConstraints) throws DebugException {
      if (expected != null) {
         TestCase.assertNotNull(current);
         // Compare stack frame
         TestCase.assertTrue(expected.getName() + " does not match " + current.getName(), StringUtil.equalIgnoreWhiteSpace(expected.getName(), current.getName()));
         TestCase.assertEquals(expected.getName(), expected.getCharStart(), current.getCharStart());
         TestCase.assertEquals(expected.getName(), expected.getCharEnd(), current.getCharEnd());
         TestCase.assertEquals(expected.getName(), expected.getLineNumber(), current.getLineNumber());
         compareDebugElement(expected, current, true, compareVariables, compareConstraints);
         if (expected.getThread() instanceof ISEThread) {
            TestCase.assertTrue(current.getThread() instanceof ISEThread);
            compareThread((ISEThread)expected.getThread(), (ISEThread)current.getThread(), false, compareVariables, compareConstraints);
         }
         else {
            compareThread(expected.getThread(), current.getThread(), false, compareVariables, compareConstraints);
         }
         // Compare variables
         if (compareVariables) {
            TestCase.assertEquals(expected.getName(), expected.hasVariables(), current.hasVariables());
            if (expected.hasVariables()) {
               IVariable[] expectedVariables = expected.getVariables();
               IVariable[] currentVariables = current.getVariables();
               compareVariables(expectedVariables, currentVariables, compareVariables, compareConstraints);
            }
         }
      }
      else {
         TestCase.assertNull(current);
      }
   }
   
   /**
    * Compares the given {@link ISEConstraint}s with each other. The order is not relevant.
    * @param expected The expected {@link ISEConstraint}s.
    * @param current The current {@link ISEConstraint}s.
    * @param compareVariables Compare variables?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareConstraints(ISEConstraint[] expected, 
                                            ISEConstraint[] current, 
                                            boolean compareVariables,
                                            boolean compareConstraints) throws DebugException {
      TestCase.assertEquals(expected.length, current.length);
      // Compare ignore order
      List<ISEConstraint> availableCurrentConstraints = new LinkedList<ISEConstraint>();
      CollectionUtil.addAll(availableCurrentConstraints, current);
      for (int i = 0; i < expected.length; i++) {
         final ISEConstraint expectedConstraint = expected[i];
         // Find current constraint with same name
         ISEConstraint currentConstraint = CollectionUtil.searchAndRemove(availableCurrentConstraints, new IFilter<ISEConstraint>() {
            @Override
            public boolean select(ISEConstraint element) {
               try {
                  return element.getName().equalsIgnoreCase(expectedConstraint.getName());
               }
               catch (DebugException e) {
                  throw new RuntimeException(e);
               }
            }
         });
         TestCase.assertNotNull(currentConstraint);
         // Compare constraints
         compareConstraint(expectedConstraint, currentConstraint, compareVariables, compareConstraints);
      }
      TestCase.assertTrue(availableCurrentConstraints.isEmpty());
   }
   
   /**
    * Compares the given {@link ISEConstraint}s with each other.
    * @param expected The expected {@link ISEConstraint}.
    * @param current The current {@link ISEConstraint}.
    * @param compareVariables Compare variables?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareConstraint(ISEConstraint expected, 
                                           ISEConstraint current, 
                                           boolean compareVariables,
                                           boolean compareConstraints) throws DebugException {
      if (expected != null) {
         TestCase.assertNotNull(current);
         // Compare variable
         TestCase.assertTrue(expected.getName() + " does not match " + current.getName(), StringUtil.equalIgnoreWhiteSpace(expected.getName(), current.getName()));
         compareDebugElement(expected, current, true, compareVariables, compareConstraints);
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
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareVariables(IVariable[] expected, IVariable[] current, boolean compareVariables, boolean compareConstraints) throws DebugException {
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
         compareVariable(expectedVariable, currentVariable, compareVariables, compareConstraints);
      }
      TestCase.assertTrue(availableCurrentVariables.isEmpty());
   }
   
   /**
    * Compares the given {@link IVariable}s with each other.
    * @param expected The expected {@link IVariable}.
    * @param current The current {@link IVariable}.
    * @param compareVariables Compare variables?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareVariable(IVariable expected, IVariable current, boolean compareVariables, boolean compareConstraints) throws DebugException {
      if (expected != null) {
         TestCase.assertNotNull(current);
         // Compare variable
         TestCase.assertTrue(expected.getName() + " does not match " + current.getName(), StringUtil.equalIgnoreWhiteSpace(expected.getName(), current.getName()));
         TestCase.assertEquals(expected.getName(), expected.getReferenceTypeName(), current.getReferenceTypeName());
         compareDebugElement(expected, current, true, compareVariables, compareConstraints);
         // Compare value
         compareValue(expected.getValue(), current.getValue(), compareVariables, compareConstraints);
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
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareValue(IValue expected, IValue current, boolean compareVariables, boolean compareConstraints) throws DebugException {
      if (expected != null) {
         TestCase.assertNotNull(current);
         // Compare value
         TestCase.assertEquals(expected.isAllocated(), current.isAllocated());
         TestCase.assertEquals(expected.getReferenceTypeName(), current.getReferenceTypeName());
         TestCase.assertTrue(expected.getValueString() + " does not match " + current.getValueString(), StringUtil.equalIgnoreWhiteSpace(expected.getValueString(), current.getValueString()));
         if (expected instanceof ISEValue) {
            TestCase.assertTrue(current instanceof ISEValue);
            TestCase.assertEquals(((ISEValue)expected).isMultiValued(), ((ISEValue)current).isMultiValued());
         }
         compareDebugElement(expected, current, true, compareVariables, compareConstraints);
         // Compare variables
         TestCase.assertEquals(expected.hasVariables(), current.hasVariables());
         if (expected.hasVariables()) {
            IVariable[] expectedVariables = expected.getVariables();
            IVariable[] currentVariables = current.getVariables();
            compareVariables(expectedVariables, currentVariables, compareVariables, compareConstraints);
         }
         // Compare constraints
         if (expected instanceof ISEValue) {
            TestCase.assertTrue(current instanceof ISEValue);
            if (compareConstraints) {
               compareConstraints(((ISEValue) expected).getRelevantConstraints(), ((ISEValue) current).getRelevantConstraints(), compareVariables, compareConstraints);
            }
         }
         else {
            TestCase.assertFalse(current instanceof ISEValue);
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
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareThread(IThread expected, IThread current, boolean compareReferences, boolean compareVariables, boolean compareConstraints) throws DebugException {
      // Compare thread
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.getName(), current.getName());
      TestCase.assertEquals(expected.getPriority(), current.getPriority());
      compareDebugElement(expected, current, compareReferences, compareVariables, compareConstraints);
      if (compareReferences) {
         // Compare contained stack frames
         TestCase.assertEquals(expected.hasStackFrames(), current.hasStackFrames());
         IStackFrame[] expectedStackFrames = expected.getStackFrames();
         IStackFrame[] currentStackFrames = current.getStackFrames();
         TestCase.assertEquals(expectedStackFrames.length, currentStackFrames.length);
         for (int i = 0; i < expectedStackFrames.length; i++) {
            compareStackFrame(expectedStackFrames[i], currentStackFrames[i], compareVariables, compareConstraints);
         }
         compareStackFrame(expected.getTopStackFrame(), current.getTopStackFrame(), compareVariables, compareConstraints);
      }
   }
   
   /**
    * Compares the given {@link ISEThread}s with each other.
    * @param expected The expected {@link ISEThread}.
    * @param current The current {@link ISEThread}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareThread(ISEThread expected, 
                                       ISEThread current, 
                                       boolean compareReferences, 
                                       boolean compareId, 
                                       boolean compareVariables,
                                       boolean compareCallStack,
                                       boolean compareConstraints) throws DebugException {
      compareThread((IThread)expected, (IThread)current, compareReferences, compareVariables, compareConstraints);
      compareStackFrame(expected, current, compareVariables, compareConstraints);
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack, compareConstraints);
      compareTerminations(expected.getTerminations(), current.getTerminations());
   }

   /**
    * Compares the given {@link ISEBranchCondition}s with each other.
    * @param expected The expected {@link ISEBranchCondition}.
    * @param current The current {@link ISEBranchCondition}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareBranchCondition(ISEBranchCondition expected, 
                                                ISEBranchCondition current, 
                                                boolean compareReferences, 
                                                boolean compareId, 
                                                boolean compareVariables,
                                                boolean compareCallStack,
                                                boolean compareConstraints) throws DebugException {
      compareStackFrame(expected, current, compareVariables, compareConstraints);
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack, compareConstraints);
   }

   /**
    * Compares the given {@link ISEBranchStatement}s with each other.
    * @param expected The expected {@link ISEBranchStatement}.
    * @param current The current {@link ISEBranchStatement}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareBranchStatement(ISEBranchStatement expected, 
                                                ISEBranchStatement current, 
                                                boolean compareReferences, 
                                                boolean compareId, 
                                                boolean compareVariables,
                                                boolean compareCallStack,
                                                boolean compareConstraints) throws DebugException {
      compareStackFrame(expected, current, compareVariables, compareConstraints);
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack, compareConstraints);
   }

   /**
    * Compares the given {@link ISEMethodCall}s with each other.
    * @param expected The expected {@link ISEMethodCall}.
    * @param current The current {@link ISEMethodCall}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareMethodCall(ISEMethodCall expected, 
                                           ISEMethodCall current, 
                                           boolean compareReferences, 
                                           boolean compareId, 
                                           boolean compareVariables,
                                           boolean compareCallStack,
                                           boolean compareConstraints) throws DebugException {
      compareStackFrame(expected, current, compareVariables, compareConstraints);
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack, compareConstraints);
      compareConditions(expected.getMethodReturnConditions(), current.getMethodReturnConditions(), compareReferences, compareId, compareVariables, compareCallStack, compareConstraints);
   }

   /**
    * Compares the given conditions.
    * @param expected The expected conditions.
    * @param current The current conditions.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareConditions(ISEBranchCondition[] expected, 
                                           ISEBranchCondition[] current, 
                                           boolean compareReferences, 
                                           boolean compareId, 
                                           boolean compareVariables, 
                                           boolean compareCallStack,
                                           boolean compareConstraints) throws DebugException {
      if (expected != null) {
         assertNotNull(current);
         assertEquals(expected.length, current.length);
         for (int i = 0; i < expected.length; i++) {
            compareBranchCondition(expected[i], current[i], false, compareId, compareVariables, compareCallStack, compareConstraints);
         }
      }
      else {
         assertNull(current);
      }
   }

   /**
    * Compares the given {@link ISELoopBodyTermination}s with each other.
    * @param expected The expected {@link ISELoopBodyTermination}.
    * @param current The current {@link ISELoopBodyTermination}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareLoopBodyTermination(ISELoopBodyTermination expected, 
                                                    ISELoopBodyTermination current, 
                                                    boolean compareReferences, 
                                                    boolean compareId, 
                                                    boolean compareVariables,
                                                    boolean compareCallStack,
                                                    boolean compareConstraints) throws DebugException {
      compareTermination(expected, current, compareReferences, compareId, compareVariables, compareCallStack, compareConstraints);
   }

   /**
    * Compares the given {@link ISEExceptionalTermination}s with each other.
    * @param expected The expected {@link ISEExceptionalTermination}.
    * @param current The current {@link ISEExceptionalTermination}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareExceptionalTermination(ISEExceptionalTermination expected, 
                                                       ISEExceptionalTermination current, 
                                                       boolean compareReferences, 
                                                       boolean compareId, 
                                                       boolean compareVariables,
                                                       boolean compareCallStack,
                                                       boolean compareConstraints) throws DebugException {
      compareTermination(expected, current, compareReferences, compareId, compareVariables, compareCallStack, compareConstraints);
   }

   /**
    * Compares the given {@link ISELoopCondition}s with each other.
    * @param expected The expected {@link ISELoopCondition}.
    * @param current The current {@link ISELoopCondition}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareLoopCondition(ISELoopCondition expected, 
                                              ISELoopCondition current, 
                                              boolean compareReferences, 
                                              boolean compareId, 
                                              boolean compareVariables,
                                              boolean compareCallStack,
                                              boolean compareConstraints) throws DebugException {
      compareStackFrame(expected, current, compareVariables, compareConstraints);
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack, compareConstraints);
   }

   /**
    * Compares the given {@link ISELoopStatement}s with each other.
    * @param expected The expected {@link ISELoopStatement}.
    * @param current The current {@link ISELoopStatement}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareLoopStatement(ISELoopStatement expected, 
                                              ISELoopStatement current, 
                                              boolean compareReferences, 
                                              boolean compareId, 
                                              boolean compareVariables,
                                              boolean compareCallStack,
                                              boolean compareConstraints) throws DebugException {
      compareStackFrame(expected, current, compareVariables, compareConstraints);
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack, compareConstraints);
   }

   /**
    * Compares the given {@link ISEMethodReturn}s with each other.
    * @param expected The expected {@link ISEMethodReturn}.
    * @param current The current {@link ISEMethodReturn}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareMethodReturn(ISEMethodReturn expected, 
                                             ISEMethodReturn current, 
                                             boolean compareReferences, 
                                             boolean compareId, 
                                             boolean compareVariables,
                                             boolean compareCallStack,
                                             boolean compareConstraints) throws DebugException {
      compareStackFrame(expected, current, compareVariables, compareConstraints);
      compareNode(expected.getMethodReturnCondition(), current.getMethodReturnCondition(), false, compareId, compareVariables, compareCallStack, compareConstraints);
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack, compareConstraints);
   }

   /**
    * Compares the given {@link ISEExceptionalMethodReturn}s with each other.
    * @param expected The expected {@link ISEExceptionalMethodReturn}.
    * @param current The current {@link ISEExceptionalMethodReturn}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareExceptionalMethodReturn(ISEExceptionalMethodReturn expected, 
                                                        ISEExceptionalMethodReturn current, 
                                                        boolean compareReferences, 
                                                        boolean compareId, 
                                                        boolean compareVariables,
                                                        boolean compareCallStack,
                                                        boolean compareConstraints) throws DebugException {
      compareStackFrame(expected, current, compareVariables, compareConstraints);
      compareNode(expected.getMethodReturnCondition(), current.getMethodReturnCondition(), false, compareId, compareVariables, compareCallStack, compareConstraints);
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack, compareConstraints);
   }

   /**
    * Compares the given {@link ISEStatement}s with each other.
    * @param expected The expected {@link ISEStatement}.
    * @param current The current {@link ISEStatement}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareStatement(ISEStatement expected, 
                                          ISEStatement current, 
                                          boolean compareReferences, 
                                          boolean compareId, 
                                          boolean compareVariables,
                                          boolean compareCallStack,
                                          boolean compareConstraints) throws DebugException {
      compareStackFrame(expected, current, compareVariables, compareConstraints);
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack, compareConstraints);
   }

   /**
    * Compares the given {@link ISEMethodContract}s with each other.
    * @param expected The expected {@link ISEMethodContract}.
    * @param current The current {@link ISEMethodContract}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareMethodContract(ISEMethodContract expected, 
                                                  ISEMethodContract current, 
                                                  boolean compareReferences, 
                                                  boolean compareId, 
                                                  boolean compareVariables,
                                                  boolean compareCallStack,
                                                  boolean compareConstraints) throws DebugException {
      compareStackFrame(expected, current, compareVariables, compareConstraints);
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack, compareConstraints);
      assertEquals(expected.isPreconditionComplied(), current.isPreconditionComplied());
      assertEquals(expected.hasNotNullCheck(), current.hasNotNullCheck());
      assertEquals(expected.isNotNullCheckComplied(), current.isNotNullCheckComplied());
   }

   /**
    * Compares the given {@link ISELoopInvariant}s with each other.
    * @param expected The expected {@link ISELoopInvariant}.
    * @param current The current {@link ISELoopInvariant}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareLoopInvariant(ISELoopInvariant expected, 
                                              ISELoopInvariant current, 
                                              boolean compareReferences, 
                                              boolean compareId, 
                                              boolean compareVariables,
                                              boolean compareCallStack,
                                              boolean compareConstraints) throws DebugException {
      compareStackFrame(expected, current, compareVariables, compareConstraints);
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack, compareConstraints);
      assertEquals(expected.isInitiallyValid(), current.isInitiallyValid());
   }

   /**
    * Compares the given {@link ISETermination}s with each other.
    * @param expected The expected {@link ISETermination}.
    * @param current The current {@link ISETermination}.
    * @param compareReferences Compare also the containment hierarchy?
    * @param compareId Compare the value of {@link ISEDebugElement#getId()}?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @param compareConstraints Compare constraints?
    * @throws DebugException Occurred Exception.
    */
   protected static void compareTermination(ISETermination expected, 
                                            ISETermination current, 
                                            boolean compareReferences, 
                                            boolean compareId, 
                                            boolean compareVariables,
                                            boolean compareCallStack,
                                            boolean compareConstraints) throws DebugException {
      compareNode(expected, current, compareReferences, compareId, compareVariables, compareCallStack, compareConstraints);
      compareStackFrame(expected, current, compareVariables, compareConstraints);
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
    * @throws DebugException Occurred Exception.
    */
   public static SWTBotTreeItem selectInDebugTree(SWTBotView debugView, int... indexPathToItem) throws DebugException {
      SWTBotTree debugTree = debugView.bot().tree();
      IDebugView view = (IDebugView)debugView.getReference().getView(true);
      TreeViewer viewer = (TreeViewer)view.getViewer();
      ILazyTreePathContentProvider lazyContentProvider = (ILazyTreePathContentProvider)viewer.getContentProvider();

      TestCase.assertNotNull(indexPathToItem);
      TestCase.assertTrue(indexPathToItem.length >= 1);
      SWTBotTreeItem item = null;
      for (int i = 1; i < indexPathToItem.length + 1; i++) {
         int[] subPath = Arrays.copyOf(indexPathToItem, i);
         item = TestUtilsUtil.selectInTree(debugTree, subPath);
         if (!item.isExpanded()) {
            item.expand();
         }
         SEDUIUtil.waitForPendingRequests(viewer, lazyContentProvider);
      }
      return item;
   }
}
