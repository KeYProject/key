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

package org.key_project.sed.key.core.test.testcase.swtbot;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.core.model.IKeYSEDDebugNode;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * Tests access of {@link ISEDDebugNode#getChildren()} from different threads
 * to make sure that in KeY's implementation no multiple {@link IKeYSEDDebugNode}s are
 * created for the same {@link IExecutionNode}.
 * @author Martin Hentschel
 */
public class SWTBotKeYModelThreadSaveChildAccessTest extends AbstractKeYDebugTargetTestCase {
   /**
    * Tests access of {@link ISEDDebugNode#getChildren()} from different threads
    * to make sure that in KeY's implementation no multiple {@link IKeYSEDDebugNode}s are
    * created for the same {@link IExecutionNode}.
    */
   @Test
   public void testChildAccessOfElseIfTest() throws Exception {
      IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
            // Get debug target TreeItem
            SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0); // Select thread
            // Resume
            resume(bot, item, target);
            // Start with threads
            List<ISEDDebugNode> toTest = new LinkedList<ISEDDebugNode>();
            CollectionUtil.addAll(toTest, target.getSymbolicThreads());
            assertFalse(toTest.isEmpty());
            // Iterate over the whole containment hierarchy
            while (!toTest.isEmpty()) {
               // Define current node
               ISEDDebugNode current = toTest.remove(0);
               // Access ISEDDebugNode#getChildren() from different threads
               ChildAccessThread[] threads = new ChildAccessThread[3];
               for (int i = 0; i < threads.length; i++) {
                  threads[i] = new ChildAccessThread(current);
               }
               for (int i = 0; i < threads.length; i++) {
                  threads[i].start();
               }
               TestUtilsUtil.waitForThreads(threads);
               // Test result
               ISEDDebugNode[] children = current.getChildren();
               assertNotNull(children);
               for (ChildAccessThread thread : threads) {
                  assertNull(thread.getException());
                  assertNotNull(thread.getChildren());
                  assertSame(children, thread.getChildren());
               }
               // Add children in test set
               CollectionUtil.addAll(toTest, children);
            }
         }
      };
      doKeYDebugTargetTest("SWTBotKeYModelThreadSaveChildAccessTest_testChildAccessOfElseIfTest",
                           "data/elseIfTest/test",
                           true,
                           true, // Must be true because otherwise instantiates the sed visualization all children!
                           createMethodSelector("ElseIfTest", "elseIf", "I"),
                           null,
                           null,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           Boolean.FALSE,
                           8,
                           executor);
   }
   
   /**
    * A {@link Thread} which executes {@link ISEDDebugNode#getChildren()}
    * and provides the result.
    * @author Martin Hentschel
    */
   private static class ChildAccessThread extends Thread {
      /**
       * The parent to execute {@link ISEDDebugNode#getChildren()} on.
       */
      private ISEDDebugNode parent;
      
      /**
       * The result of The parent to execute {@link ISEDDebugNode#getChildren()} on.
       */
      private ISEDDebugNode[] children;
      
      /**
       * The occurred exception or {@code null} if access was successful.
       */
      private DebugException exception;
      
      /**
       * Constructor. 
       * @param parent The parent to execute {@link ISEDDebugNode#getChildren()} on.
       */
      public ChildAccessThread(ISEDDebugNode parent) {
         super();
         this.parent = parent;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void run() {
         try {
            children = parent.getChildren();
         }
         catch (DebugException e) {
            exception = e;
         }
      }

      /**
       * Returns the result of The parent to execute {@link ISEDDebugNode#getChildren()} on.
       * @return The result of The parent to execute {@link ISEDDebugNode#getChildren()} on.
       */
      public ISEDDebugNode[] getChildren() {
         return children;
      }

      /**
       * Returns the occurred exception or {@code null} if access was successful.
       * @return The occurred exception or {@code null} if access was successful.
       */
      public DebugException getException() {
         return exception;
      }
   }
}