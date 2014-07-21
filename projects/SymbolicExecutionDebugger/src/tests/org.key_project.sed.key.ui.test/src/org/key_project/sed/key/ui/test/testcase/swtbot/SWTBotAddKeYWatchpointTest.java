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

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.SWTBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotStyledText;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotText;
import org.junit.Test;
import org.key_project.sed.key.core.test.util.TestBreakpointsUtil;
import org.key_project.sed.key.ui.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class SWTBotAddKeYWatchpointTest extends TestCase {
   public static final String ADD_WATCHPOINT_TOOLTIP = "Add a KeY Watchpoint.";

   private static boolean projectExists = false;

   @Test
   public void testOpensDialog() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      if (!projectExists) {
         initializeProject();
      }
      TestBreakpointsUtil.openBreakpointView(bot);
      TestUtilsUtil.clickDirectly(bot.toolbarButtonWithTooltip(ADD_WATCHPOINT_TOOLTIP));
      SWTBotShell addWatchpointShell = bot.activeShell();
      assertEquals("Add KeY Watchpoint", addWatchpointShell.getText());
      TestUtilsUtil.clickDirectly(bot, "Cancel");
      // close all shells
      bot.closeAllShells();
      // Close all editors
      bot.closeAllEditors();
   }

   @Test
   public void testTypeNotValid() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      if (!projectExists) {
         initializeProject();
      }
      TestUtilsUtil.openView("org.eclipse.debug.ui.BreakpointView");
      TestUtilsUtil.clickDirectly(bot
            .toolbarButtonWithTooltip(ADD_WATCHPOINT_TOOLTIP));
      bot.text(0).setText("invalidType");
      assertFalse(bot.button("OK").isEnabled());
      assertFalse(bot.styledText().isEnabled());
      TestUtilsUtil.clickDirectly(bot, "Cancel");
      // close all shells
      bot.closeAllShells();
      // Close all editors
      bot.closeAllEditors();
   }

   @Test
   public void testTypeValidNoCondition() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      if (!projectExists) {
         initializeProject();
      }
      TestUtilsUtil.openView("org.eclipse.debug.ui.BreakpointView");
      TestUtilsUtil.clickDirectly(bot
            .toolbarButtonWithTooltip(ADD_WATCHPOINT_TOOLTIP));
      bot.text(0).setText("EmptyTestClass");
      assertFalse(bot.button("OK").isEnabled());
      assertTrue(bot.styledText().isEnabled());
      TestUtilsUtil.clickDirectly(bot, "Cancel");
      // close all shells
      bot.closeAllShells();
      // Close all editors
      bot.closeAllEditors();
   }

   @Test
   public void testTypeValidOnlySpacesInCondition() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      if (!projectExists) {
         initializeProject();
      }
      TestUtilsUtil.openView("org.eclipse.debug.ui.BreakpointView");
      TestUtilsUtil.clickDirectly(bot
            .toolbarButtonWithTooltip(ADD_WATCHPOINT_TOOLTIP));
      bot.text(0).setText("EmptyTestClass");
      SWTBotStyledText styledText = bot.styledText(0);
      styledText.setText("     ");
      assertFalse(bot.button("OK").isEnabled());
      TestUtilsUtil.clickDirectly(bot, "Cancel");
      // close all shells
      bot.closeAllShells();
      // Close all editors
      bot.closeAllEditors();
   }

   @Test
   public void testTypeValidAnyNonEmptyCondition() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      if (!projectExists) {
         initializeProject();
      }
      TestUtilsUtil.openView("org.eclipse.debug.ui.BreakpointView");
      TestUtilsUtil.clickDirectly(bot.toolbarButtonWithTooltip(ADD_WATCHPOINT_TOOLTIP));
      bot.text(0).setText("EmptyTestClass");
      SWTBotStyledText styledText = bot.styledText(0);
      styledText.setText("anyNonEmptyCondition");
      assertTrue(bot.button("OK").isEnabled());
      TestUtilsUtil.clickDirectly(bot, "Cancel");
      // close all shells
      bot.closeAllShells();
      // Close all editors
      bot.closeAllEditors();
   }

   @Test
   public void testInitialType() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      if (!projectExists) {
         initializeProject();
      }
      IPath classPath = new Path(ResourcesPlugin.getWorkspace().getRoot().getRawLocation().toString() + "/SWTBotAddKeYWatchpointTest/src/EmptyTestClass.java");
      IFile classFile = ResourcesPlugin.getWorkspace().getRoot().getFileForLocation(classPath);
      TestUtilsUtil.openEditor(classFile);
      TestUtilsUtil.openView("org.eclipse.debug.ui.BreakpointView");
      TestUtilsUtil.clickDirectly(bot.toolbarButtonWithTooltip(ADD_WATCHPOINT_TOOLTIP));
      SWTBotShell addWatchpointShell = bot.activeShell();
      assertEquals("EmptyTestClass", bot.text().getText());
      SWTBotStyledText styledText = bot.styledText();
      assertTrue(styledText.isEnabled());
      TestUtilsUtil.clickDirectly(bot, "Browse");
      SWTBot dialogBot = bot.activeShell().bot();
      assertEquals("EmptyTestClass", dialogBot.text().getText());
      TestUtilsUtil.clickDirectly(dialogBot, "Cancel");
      addWatchpointShell.setFocus();
      TestUtilsUtil.clickDirectly(bot, "Cancel");
      bot.activeEditor().toTextEditor().close();
      // close all shells
      bot.closeAllShells();
      // Close all editors
      bot.closeAllEditors();
   }

   @Test
   public void testBrowseTypeWithoutInitialType() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      if (!projectExists) {
         initializeProject();
      }
      TestUtilsUtil.openView("org.eclipse.debug.ui.BreakpointView");
      TestUtilsUtil.clickDirectly(bot.toolbarButtonWithTooltip(ADD_WATCHPOINT_TOOLTIP));
      SWTBotShell addWatchpointShell = bot.activeShell();
      TestUtilsUtil.clickDirectly(bot, "Browse");
      SWTBotShell dialogShell = bot.activeShell();
      SWTBot dialogBot = dialogShell.bot();
      bot.sleep(10000);
      assertEquals("Select class for KeY Watchpoint", dialogShell.getText());
      SWTBotText typeText = bot.text();
      assertEquals("", typeText.getText());
      assertFalse(dialogBot.button("OK").isEnabled());
      typeText.setText(" ");
      bot.sleep(100);
      assertFalse(dialogBot.button("OK").isEnabled());
      typeText.setText("EmptyTestClass");
      bot.sleep(100);
      assertTrue(dialogBot.button("OK").isEnabled());
      TestUtilsUtil.clickDirectly(dialogBot, "OK");
      addWatchpointShell.setFocus();
      assertEquals("EmptyTestClass", bot.text().getText());
      TestUtilsUtil.clickDirectly(bot, "Cancel");
      // close all shells
      bot.closeAllShells();
      // Close all editors
      bot.closeAllEditors();
   }

   @Test
   public void testWatchpointExistsAfterOK() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      if (!projectExists) {
         initializeProject();
      }
      TestUtilsUtil.openView("org.eclipse.debug.ui.BreakpointView");
      assertFalse(bot.tree().hasItems());
      TestUtilsUtil.clickDirectly(bot.toolbarButtonWithTooltip(ADD_WATCHPOINT_TOOLTIP));
      bot.text().setText("EmptyTestClass");
      SWTBotStyledText styledText = bot.styledText(0);
      styledText.setText("anyNonEmptyCondition");
      TestUtilsUtil.clickDirectly(bot, "OK");
      TestUtilsUtil.openView("org.eclipse.debug.ui.BreakpointView");
      assertTrue(bot.tree().hasItems());
      assertEquals(1, bot.tree().getAllItems().length);
      // close all shells
      bot.closeAllShells();
      // Close all editors
      bot.closeAllEditors();
   }

   private void initializeProject() throws Exception{
      IJavaProject project = TestUtilsUtil.createJavaProject("SWTBotAddKeYWatchpointTest");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/AddKeYWatchpoints/test", project.getProject().getFolder("src"));
      projectExists=true;
   }
}