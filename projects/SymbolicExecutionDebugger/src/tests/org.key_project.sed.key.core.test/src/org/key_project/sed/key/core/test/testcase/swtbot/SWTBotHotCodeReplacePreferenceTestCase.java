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

package org.key_project.sed.key.core.test.testcase.swtbot;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.internal.debug.ui.IJDIPreferencesConstants;
import org.eclipse.jdt.internal.debug.ui.JDIDebugUIPlugin;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.util.test.util.TestUtilsUtil;

@SuppressWarnings("restriction")
public class SWTBotHotCodeReplacePreferenceTestCase extends
      AbstractKeYDebugTargetTestCase {

   @Test
   public void testHotCodeReplace() throws Exception{
      IKeYDebugTargetTestExecutor executor = new AbstractKeYDebugTargetTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
            IPath classPath = new Path(ResourcesPlugin.getWorkspace().getRoot().getRawLocation().toString() + "/SWTBotHotCodeReplacePreferenceTestCase_testHotCodeReplace/src/CodeReplace.java");
            IFile classFile = ResourcesPlugin.getWorkspace().getRoot().getFileForLocation(classPath);
            TestUtilsUtil.openEditor(classFile);
            ErrorDialog.AUTOMATED_MODE=false;
            SWTBotEclipseEditor editor = bot.activeEditor().toTextEditor(); 
            editor.setText(editor.getText()+" ");
            SWTBotShell eclipseShell = bot.activeShell();
            assertTrue(JDIDebugUIPlugin.getDefault().getPreferenceStore().getBoolean(IJDIPreferencesConstants.PREF_ALERT_HCR_NOT_SUPPORTED));
            editor.save();
            SWTBotShell hotCodeReplaceDialog = bot.activeShell();
            assertTrue(hotCodeReplaceDialog.isOpen());
            assertTrue(hotCodeReplaceDialog.isActive());
            bot.checkBox("Do not show error when hot code replace is not supported").click();
            TestUtilsUtil.clickDirectly(bot, "Continue");
            assertFalse(hotCodeReplaceDialog.isOpen());
            assertFalse(target.isTerminated());
            assertFalse(target.isDisconnected());
            assertFalse(JDIDebugUIPlugin.getDefault().getPreferenceStore().getBoolean(IJDIPreferencesConstants.PREF_ALERT_HCR_NOT_SUPPORTED));
            editor.setText(editor.getText()+" ");
            editor.save();
            assertEquals(bot.activeShell().getText(), eclipseShell.getText());
            JDIDebugUIPlugin.getDefault().getPreferenceStore().setValue(IJDIPreferencesConstants.PREF_ALERT_HCR_NOT_SUPPORTED, true);
         }
      };
      doKeYDebugTargetTest("SWTBotHotCodeReplacePreferenceTestCase_testHotCodeReplace",
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