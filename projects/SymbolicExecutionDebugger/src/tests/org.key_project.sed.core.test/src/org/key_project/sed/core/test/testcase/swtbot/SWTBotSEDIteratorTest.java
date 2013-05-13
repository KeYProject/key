/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

import junit.framework.TestCase;

import org.eclipse.debug.core.DebugException;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.core.util.ISEDIterator;
import org.key_project.sed.core.util.SEDPreferenceUtil;
import org.key_project.sed.core.util.SEDPreorderIterator;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for {@link SEDPreorderIterator}.
 * @author Martin Hentschel
 */
public class SWTBotSEDIteratorTest extends TestCase {
   /**
    * Makes sure that all children of an {@link ISEDDebugTarget} are
    * traversed by {@link SEDPreorderIterator} in the correct order. The tested
    * methods are {@link SEDPreorderIterator#hasNext()} and {@link SEDPreorderIterator#next()}.
    */
   @Test
   public void testNext() throws Exception {
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
         ISEDDebugTarget target = TestSedCoreUtil.waitUntilDebugTreeHasDebugTarget(bot, debugTree);
         // Test iterator
         ISEDIterator iterator = new SEDPreorderIterator(target);
         assertTrue(iterator.hasNext());
         assertNext(target, iterator);
         assertFalse(iterator.hasNext());
      }
      finally {
         SEDPreferenceUtil.setShowCompactExecutionTree(originalCompactView);
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
         TestUtilsUtil.openPerspective(defaultPerspective);
      }
   }

   protected void assertNext(ISEDDebugTarget target, ISEDIterator iterator) throws DebugException {
      assertNotNull(target);
      assertTrue(iterator.hasNext());
      ISEDDebugElement next = iterator.next();
      assertSame(target, next);
      for (ISEDThread thread : target.getSymbolicThreads()) {
         assertNext(thread, iterator);
      }
   }

   protected void assertNext(ISEDDebugNode node, ISEDIterator iterator) throws DebugException {
      assertNotNull(node);
      assertTrue(iterator.hasNext());
      ISEDDebugElement next = iterator.next();
      assertSame(node, next);
      for (ISEDDebugNode child : node.getChildren()) {
         assertNext(child, iterator);
      }
   }
}