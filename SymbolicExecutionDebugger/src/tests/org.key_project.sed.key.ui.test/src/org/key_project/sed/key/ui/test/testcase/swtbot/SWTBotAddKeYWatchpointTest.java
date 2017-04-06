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

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.SWTBot;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.*;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.core.test.util.TestBreakpointsUtil;
import org.key_project.sed.key.ui.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import junit.framework.TestCase;

public class SWTBotAddKeYWatchpointTest extends TestCase {
   public static final String ADD_WATCHPOINT_ID = "org.key_project.sed.key.ui.addWatchpointCommand";

   private static boolean projectExists = false;
   
   private IPerspectiveDescriptor originalPerspective;
   
   @Before
   @Override
   public void setUp() throws Exception {
      TestUtilsUtil.closeWelcomeView();
      originalPerspective = TestUtilsUtil.getActivePerspective();
      TestSedCoreUtil.openSymbolicDebugPerspective(new SWTWorkbenchBot());
   }

   @After
   @Override
   public void tearDown() throws Exception {
      TestUtilsUtil.openPerspective(originalPerspective);
      super.tearDown();
   }

   @Test
   public void testOpensDialog() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      if (!projectExists) {
         initializeProject();
      }
      SWTBotView view = TestBreakpointsUtil.openBreakpointView(bot);
      SWTBotToolbarButton addButton = TestUtilsUtil.getToolbarButtonWithId(view, ADD_WATCHPOINT_ID);
      TestUtilsUtil.clickDirectly(addButton);
      SWTBotShell addWatchpointShell = bot.shell("Add KeY Watchpoint");
      assertEquals("Add KeY Watchpoint", addWatchpointShell.getText());
      TestUtilsUtil.clickDirectly(addWatchpointShell.bot(), "Cancel");
      // Close all editors
      assertEquals(0, view.bot().tree().getAllItems().length);
      bot.closeAllEditors();
   }

   @Test
   public void testTypeNotValid() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      if (!projectExists) {
         initializeProject();
      }
      SWTBotView view = TestBreakpointsUtil.openBreakpointView(bot);
      SWTBotToolbarButton addButton = TestUtilsUtil.getToolbarButtonWithId(view, ADD_WATCHPOINT_ID);
      TestUtilsUtil.clickDirectly(addButton);
      SWTBotShell addWatchpointShell = bot.shell("Add KeY Watchpoint");
      addWatchpointShell.bot().text(0).setText("invalidType");
      assertFalse(addWatchpointShell.bot().button("OK").isEnabled());
      assertFalse(addWatchpointShell.bot().styledText().isEnabled());
      TestUtilsUtil.clickDirectly(addWatchpointShell.bot(), "Cancel");
      // Close all editors
      assertEquals(0, view.bot().tree().getAllItems().length);
      bot.closeAllEditors();
   }

   @Test
   public void testTypeValidNoCondition() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      if (!projectExists) {
         initializeProject();
      }
      SWTBotView view = TestBreakpointsUtil.openBreakpointView(bot);
      SWTBotToolbarButton addButton = TestUtilsUtil.getToolbarButtonWithId(view, ADD_WATCHPOINT_ID);
      TestUtilsUtil.clickDirectly(addButton);
      SWTBotShell addWatchpointShell = bot.shell("Add KeY Watchpoint");
      addWatchpointShell.bot().text(0).setText("EmptyTestClass");
      assertFalse(addWatchpointShell.bot().button("OK").isEnabled());
      assertTrue(addWatchpointShell.bot().styledText().isEnabled());
      TestUtilsUtil.clickDirectly(addWatchpointShell.bot(), "Cancel");
      // Close all editors
      assertEquals(0, view.bot().tree().getAllItems().length);
      bot.closeAllEditors();
   }

   @Test
   public void testTypeValidOnlySpacesInCondition() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      if (!projectExists) {
         initializeProject();
      }
      SWTBotView view = TestBreakpointsUtil.openBreakpointView(bot);
      SWTBotToolbarButton addButton = TestUtilsUtil.getToolbarButtonWithId(view, ADD_WATCHPOINT_ID);
      TestUtilsUtil.clickDirectly(addButton);
      SWTBotShell addWatchpointShell = bot.shell("Add KeY Watchpoint");
      addWatchpointShell.bot().text(0).setText("EmptyTestClass");
      SWTBotStyledText styledText = addWatchpointShell.bot().styledText(0);
      styledText.setText("     ");
      assertFalse(addWatchpointShell.bot().button("OK").isEnabled());
      TestUtilsUtil.clickDirectly(addWatchpointShell.bot(), "Cancel");
      assertEquals(0, view.bot().tree().getAllItems().length);
      // Close all editors
      bot.closeAllEditors();
   }

   @Test
   public void testTypeValidAnyNonEmptyCondition() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      if (!projectExists) {
         initializeProject();
      }
      SWTBotView view = TestBreakpointsUtil.openBreakpointView(bot);
      SWTBotToolbarButton addButton = TestUtilsUtil.getToolbarButtonWithId(view, ADD_WATCHPOINT_ID);
      TestUtilsUtil.clickDirectly(addButton);
      SWTBotShell addWatchpointShell = bot.shell("Add KeY Watchpoint");
      addWatchpointShell.bot().text(0).setText("EmptyTestClass");
      SWTBotStyledText styledText = addWatchpointShell.bot().styledText(0);
      styledText.setText("anyNonEmptyCondition");
      assertTrue(addWatchpointShell.bot().button("OK").isEnabled());
      TestUtilsUtil.clickDirectly(addWatchpointShell.bot(), "Cancel");
      assertEquals(0, view.bot().tree().getAllItems().length);
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
      SWTBotView view = TestBreakpointsUtil.openBreakpointView(bot);
      SWTBotToolbarButton addButton = TestUtilsUtil.getToolbarButtonWithId(view, ADD_WATCHPOINT_ID);
      TestUtilsUtil.clickDirectly(addButton);
      SWTBotShell addWatchpointShell = bot.shell("Add KeY Watchpoint");
      assertEquals("EmptyTestClass", addWatchpointShell.bot().text().getText());
      SWTBotStyledText styledText = addWatchpointShell.bot().styledText();
      assertTrue(styledText.isEnabled());
      TestUtilsUtil.clickDirectly(addWatchpointShell.bot(), "Browse");
      SWTBot dialogBot = bot.shell("Select class for KeY Watchpoint").bot();
      assertEquals("EmptyTestClass", dialogBot.text().getText());
      TestUtilsUtil.clickDirectly(dialogBot, "Cancel");
      TestUtilsUtil.clickDirectly(addWatchpointShell.bot(), "Cancel");
      bot.activeEditor().toTextEditor().close();
      assertEquals(0, view.bot().tree().getAllItems().length);
      // Close all editors
      bot.closeAllEditors();
   }

   @Test
   public void testBrowseTypeWithoutInitialType() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      if (!projectExists) {
         initializeProject();
      }
      SWTBotView view = TestBreakpointsUtil.openBreakpointView(bot);
      SWTBotToolbarButton addButton = TestUtilsUtil.getToolbarButtonWithId(view, ADD_WATCHPOINT_ID);
      TestUtilsUtil.clickDirectly(addButton);
      SWTBotShell addWatchpointShell = bot.shell("Add KeY Watchpoint");
      TestUtilsUtil.clickDirectly(addWatchpointShell.bot(), "Browse");
      SWTBotShell dialogShell = bot.shell("Select class for KeY Watchpoint");
      SWTBot dialogBot = dialogShell.bot();
      assertEquals("Select class for KeY Watchpoint", dialogShell.getText());
      SWTBotText typeText = dialogBot.text();
      assertEquals("", typeText.getText());
      dialogBot.waitWhile(Conditions.widgetIsEnabled(dialogBot.button("OK")));
      assertFalse(dialogBot.button("OK").isEnabled());
      typeText.setText(" ");
      dialogBot.waitWhile(Conditions.widgetIsEnabled(dialogBot.button("OK")));
      assertFalse(dialogBot.button("OK").isEnabled());
      typeText.setText("EmptyTestClass");
      dialogBot.waitUntil(Conditions.widgetIsEnabled(dialogBot.button("OK")));
      assertTrue(dialogBot.button("OK").isEnabled());
      TestUtilsUtil.clickDirectly(dialogBot, "OK");
      assertEquals("EmptyTestClass", addWatchpointShell.bot().text().getText());
      TestUtilsUtil.clickDirectly(addWatchpointShell.bot(), "Cancel");
      assertEquals(0, view.bot().tree().getAllItems().length);
      // Close all editors
      bot.closeAllEditors();
   }

   @Test
   public void testWatchpointExistsAfterOK() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      if (!projectExists) {
         initializeProject();
      }
      SWTBotView view = TestBreakpointsUtil.openBreakpointView(bot);
      assertFalse(view.bot().tree().hasItems());
      SWTBotToolbarButton addButton = TestUtilsUtil.getToolbarButtonWithId(view, ADD_WATCHPOINT_ID);
      TestUtilsUtil.clickDirectly(addButton);
      SWTBotShell addWatchpointShell = bot.shell("Add KeY Watchpoint");
      addWatchpointShell.bot().text().setText("EmptyTestClass");
      SWTBotStyledText styledText = addWatchpointShell.bot().styledText(0);
      styledText.setText("anyNonEmptyCondition");
      TestUtilsUtil.clickDirectly(addWatchpointShell.bot(), "OK");
      assertTrue(view.bot().tree().hasItems());
      SWTBotTreeItem[] allBreakpointItems = view.bot().tree().getAllItems();
      assertEquals(1, allBreakpointItems.length);
      // Remove created breakpoint
      allBreakpointItems[0].contextMenu("Remove").click();
      assertEquals(0, view.bot().tree().getAllItems().length);
      // Close all editors
      bot.closeAllEditors();
   }

   private void initializeProject() throws Exception{
      IJavaProject project = TestUtilsUtil.createJavaProject("SWTBotAddKeYWatchpointTest");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/AddKeYWatchpoints/test", project.getProject().getFolder("src"));
      projectExists=true;
   }
}