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

package org.key_project.sed.core.test.testcase.swtbot;

import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.core.util.SEDPreferenceUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Makes sure that the hierarchy of symbolic execution trees is correctly
 * shown in the debug view of the Eclipse debug API.
 * @author Martin Hentschel
 */
public class SWTBotDebugViewHierarchyTest extends AbstractSetupTestCase {
   /**
    * Makes sure that the tree is updated when the user switches between
    * normal and compact view.
    */
   @Test
   public void testSwitchingBetweenCompactAndNormalHierarchy() throws Exception {
      // Close welcome view
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      IPerspectiveDescriptor defaultPerspective = TestUtilsUtil.getActivePerspective();
      // Disable compact view
      boolean originalCompactView = SEDPreferenceUtil.isShowCompactExecutionTree();
      SEDPreferenceUtil.setShowCompactExecutionTree(true);
      SWTBotTree debugTree = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Open symbolic debug perspective
         TestSedCoreUtil.openSymbolicDebugPerspective();
         // Launch fixed example
         TestSedCoreUtil.launchFixedExample();
         // Find the launched ILaunch in the debug view
         SWTBotView debugView = TestSedCoreUtil.getDebugView(bot);
         debugTree = debugView.bot().tree();
         TestSedCoreUtil.waitUntilDebugTreeHasDebugTarget(bot, debugTree);
         // Expand all tree items
         TestUtilsUtil.expandAll(debugTree);
         TestSedCoreUtil.waitForDebugTreeInterface(); // Give the user interface the chance to update the tree
         // Make sure that the correct items are shown
         TestSedCoreUtil.assertCompactFixedExample(debugTree);
         // Change to normal view
         SEDPreferenceUtil.toggleShowCompactExecutionTreePreference();
         TestSedCoreUtil.waitForDebugTreeInterface(); // Give the user interface the chance to update the tree
         // Expand all tree items
         TestUtilsUtil.expandAll(debugTree);
         TestSedCoreUtil.waitForDebugTreeInterface(); // Give the user interface the chance to update the tree
         // Make sure that the correct items are shown
         TestSedCoreUtil.assertFixedExample(debugTree);
         // Change to compact view
         SEDPreferenceUtil.toggleShowCompactExecutionTreePreference();
         TestSedCoreUtil.waitForDebugTreeInterface(); // Give the user interface the chance to update the tree
         // Expand all tree items
         TestUtilsUtil.expandAll(debugTree);
         TestSedCoreUtil.waitForDebugTreeInterface(); // Give the user interface the chance to update the tree
         // Make sure that the correct items are shown
         TestSedCoreUtil.assertCompactFixedExample(debugTree);
      }
      finally {
         SEDPreferenceUtil.setShowCompactExecutionTree(originalCompactView);
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
         TestUtilsUtil.openPerspective(defaultPerspective);
      }
   }
   
   /**
    * Makes sure that the defined hierarchy by the interface
    * {@link ISEDDebugElement} and his sub interfaces is correctly shown
    * in the debug view of the Eclipse debug API with activated
    * compact symbolic execution tree option.
    */
   @Test
   public void testCompactHierarchy() throws Exception {
      // Close welcome view
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      IPerspectiveDescriptor defaultPerspective = TestUtilsUtil.getActivePerspective();
      // Disable compact view
      boolean originalCompactView = SEDPreferenceUtil.isShowCompactExecutionTree();
      SEDPreferenceUtil.setShowCompactExecutionTree(true);
      SWTBotTree debugTree = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Open symbolic debug perspective
         TestSedCoreUtil.openSymbolicDebugPerspective();
         // Launch fixed example
         TestSedCoreUtil.launchFixedExample();
         // Find the launched ILaunch in the debug view
         SWTBotView debugView = TestSedCoreUtil.getDebugView(bot);
         debugTree = debugView.bot().tree();
         TestSedCoreUtil.waitUntilDebugTreeHasDebugTarget(bot, debugTree);
         // Expand all tree items
         TestUtilsUtil.expandAll(debugTree);
         TestSedCoreUtil.waitForDebugTreeInterface(); // Give the user interface the chance to update the tree
         // Make sure that the correct items are shown
         TestSedCoreUtil.assertCompactFixedExample(debugTree);
      }
      finally {
         SEDPreferenceUtil.setShowCompactExecutionTree(originalCompactView);
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
         TestUtilsUtil.openPerspective(defaultPerspective);
      }
   }
   
   /**
    * Makes sure that the defined hierarchy by the interface
    * {@link ISEDDebugElement} and his sub interfaces is correctly shown
    * in the debug view of the Eclipse debug API.
    */
   @Test
   public void testHierarchy() throws Exception {
      // Close welcome view
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      IPerspectiveDescriptor defaultPerspective = TestUtilsUtil.getActivePerspective();
      // Disable compact view
      boolean originalCompactView = SEDPreferenceUtil.isShowCompactExecutionTree();
      SEDPreferenceUtil.setShowCompactExecutionTree(false);
      SWTBotTree debugTree = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Open symbolic debug perspective
         TestSedCoreUtil.openSymbolicDebugPerspective();
         // Launch fixed example
         TestSedCoreUtil.launchFixedExample();
         // Find the launched ILaunch in the debug view
         SWTBotView debugView = TestSedCoreUtil.getDebugView(bot);
         debugTree = debugView.bot().tree();
         TestSedCoreUtil.waitUntilDebugTreeHasDebugTarget(bot, debugTree);
         // Expand all tree items
         TestUtilsUtil.expandAll(debugTree);
         TestSedCoreUtil.waitForDebugTreeInterface(); // Give the user interface the chance to update the tree
         // Make sure that the correct items are shown
         TestSedCoreUtil.assertFixedExample(debugTree);
      }
      finally {
         SEDPreferenceUtil.setShowCompactExecutionTree(originalCompactView);
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
         TestUtilsUtil.openPerspective(defaultPerspective);
      }
   }
}