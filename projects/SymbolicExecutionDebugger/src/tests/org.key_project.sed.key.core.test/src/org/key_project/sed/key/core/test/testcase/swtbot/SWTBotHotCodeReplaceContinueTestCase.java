package org.key_project.sed.key.core.test.testcase.swtbot;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.util.test.util.TestUtilsUtil;

public class SWTBotHotCodeReplaceContinueTestCase extends
      AbstractKeYDebugTargetTestCase {

   @Test
   public void testHotCodeReplace() throws Exception{
      IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
            IPath classPath = new Path(ResourcesPlugin.getWorkspace().getRoot().getRawLocation().toString() + "/SWTBotHotCodeReplaceContinueTestCase_testHotCodeReplace/src/CodeReplace.java");
            IFile classFile = ResourcesPlugin.getWorkspace().getRoot().getFileForLocation(classPath);
            TestUtilsUtil.openEditor(classFile);
            ErrorDialog.AUTOMATED_MODE=false;
            SWTBotEclipseEditor editor = bot.activeEditor().toTextEditor(); 
            editor.setText(editor.getText()+" ");
            editor.save();
            SWTBotShell hotCodeReplaceDialog = bot.activeShell();
            assertTrue(hotCodeReplaceDialog.isOpen());
            assertTrue(hotCodeReplaceDialog.isActive());
            TestUtilsUtil.clickDirectly(bot, "Continue");
            assertFalse(hotCodeReplaceDialog.isOpen());
            assertFalse(target.isTerminated());
            assertFalse(target.isDisconnected());
         }
      };
      doKeYDebugTargetTest("SWTBotHotCodeReplaceContinueTestCase_testHotCodeReplace",
            "data/HotCodeReplace/test",
            true,
            true,
            createMethodSelector("CodeReplace", "main"),
            null,
            null,
            Boolean.FALSE,
            Boolean.FALSE,
            Boolean.FALSE,
            Boolean.FALSE,
            Boolean.FALSE,
            8,
            executor);   
   
   }
}
