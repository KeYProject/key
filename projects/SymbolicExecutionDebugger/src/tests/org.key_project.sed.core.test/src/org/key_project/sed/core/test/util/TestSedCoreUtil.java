package org.key_project.sed.core.test.util;

import junit.framework.TestCase;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.core.model.IStackFrame;
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
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.texteditor.ITextEditor;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDBranchNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDExceptionalTermination;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.util.LaunchUtil;
import org.key_project.sed.core.util.SEDPreferenceUtil;
import org.key_project.sed.ui.perspective.SymbolicDebugPerspectiveFactory;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.java.thread.AbstractRunnableWithException;
import org.key_project.util.java.thread.IRunnableWithException;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Provides static methods that makes testing easier
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public final class TestSedCoreUtil {
   /**
    * Waiting time of the user interface.
    */
   public static final int USER_INTERFACE_DEBUG_TREE_WAIT_TIME = 1000;
   
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
    * @throws CoreException Occurred Exception.
    */
   public static void launchFixedExample() throws CoreException {
      ILaunchConfiguration config = getFixedExampleLaunchConfiguration();
      DebugUITools.launch(config, FIXED_EXAMPLE_MODE);
   }

   /**
    * Opens the "Symbolic Debug" perspective.
    * @throws Exception Occurred Exception.
    */
   public static void openSymbolicDebugPerspective() throws Exception {
      IRunnableWithException run = new AbstractRunnableWithException() {
         @Override
         public void run() {
            try {
               String perspectiveId = SymbolicDebugPerspectiveFactory.PERSPECTIVE_ID;
               IPerspectiveDescriptor perspective = PlatformUI.getWorkbench().getPerspectiveRegistry().findPerspectiveWithId(perspectiveId);
               TestCase.assertNotNull(perspective);
               IWorkbenchPage activePage = WorkbenchUtil.getActivePage();
               TestCase.assertNotNull(activePage);
               activePage.setPerspective(perspective);
               TestCase.assertEquals(perspective, activePage.getPerspective());
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
      // Assert statement2
      SWTBotTreeItem[] statement2Items = statement1Items[0].getItems();
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
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(callItems[0]) instanceof ISEDBranchNode);
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
      TestCase.assertEquals("<end>", positiveTerminationItems[0].getText());
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
      // Assert statement1, 2 and 3
      SWTBotTreeItem[] statementItems = threadItems[0].getItems();
      TestCase.assertEquals(3, statementItems.length);
      TestCase.assertEquals("int x = 1;", statementItems[0].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statementItems[0]) instanceof ISEDStatement);
      TestCase.assertEquals(0, statementItems[0].getItems().length);
      TestCase.assertEquals("int y = 2;", statementItems[1].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statementItems[1]) instanceof ISEDStatement);
      TestCase.assertEquals(0, statementItems[1].getItems().length);
      TestCase.assertEquals("int result = (x + y) / z;", statementItems[2].getText());
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(statementItems[2]) instanceof ISEDStatement);
      // Assert branch conditions
      SWTBotTreeItem[] conditions1Items = statementItems[2].getItems();
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
      TestCase.assertTrue(TestUtilsUtil.getTreeItemData(branchNotZeroItems[1]) instanceof ISEDBranchNode);
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
      TestCase.assertEquals("<end>", positiveItems[1].getText());
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
            SWTBotShell dialog = bot.shell("Terminate and Remove");
            dialog.bot().button("Yes").click();
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
         SWTBotTreeItem[] rootItems = debugTree.getAllItems();
         if (rootItems != null && rootItems.length >= 1) {
            SWTBotTreeItem[] level1Items = rootItems[0].getItems();
            if (level1Items != null && level1Items.length >= 1) {
               Object data = TestUtilsUtil.getTreeItemData(level1Items[0]);
               if (data instanceof ISEDDebugTarget) {
                  target = (ISEDDebugTarget)data;
                  return true;
               }
               else {
                  return false;
               }
            }
            else {
               return false;
            }
         }
         else {
            return false;
         }
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
}
