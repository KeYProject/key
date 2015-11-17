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

package org.key_project.sed.core.test.testcase;

import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;

import org.eclipse.debug.core.DebugException;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDebugElement;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.model.memory.ISEMemoryNode;
import org.key_project.sed.core.model.memory.SEMemoryDebugTarget;
import org.key_project.sed.core.model.memory.SEMemoryStatement;
import org.key_project.sed.core.model.memory.SEMemoryThread;
import org.key_project.sed.core.util.ISEIterator;
import org.key_project.util.test.testcase.AbstractSetupTestCase;

/**
 * Provides the basic methods a {@link TestCase} of an
 * {@link ISEIterator} implementation needs.
 * @author Martin Hentschel
 */
public abstract class AbstractSEIteratorTest extends AbstractSetupTestCase {
   /**
    * Tests one empty {@link ISENode} only for debugging purpose.
    */
   @Test
   public void testEmptyNode() throws DebugException {
      // Create tree to test
      SEMemoryDebugTarget target = appendDebugTarget("target");
      SEMemoryThread thread1 = appendThread(target, "T1");
      appendStatement(target, thread1, thread1, "T1S1");
      appendStatement(target, thread1, thread1, "T1S2");
      appendStatement(target, thread1, thread1, "T1S3");
      SEMemoryThread thread2 = appendThread(target, "T2");
      SEMemoryStatement t2s1 = appendStatement(target, thread2, thread2, "T2S1");
      // Test tree
      assertTarget(t2s1, createExpectedNode("T2S1"));
   }
   
   /**
    * Tests one empty {@link ISEThread} only for debugging purpose.
    */
   @Test
   public void testEmptyThread() throws DebugException {
      // Create tree to test
      SEMemoryDebugTarget target = appendDebugTarget("target");
      SEMemoryThread t1 = appendThread(target, "T1");
      appendThread(target, "T2");
      appendThread(target, "T3");
      // Test tree
      assertTarget(t1, createExpectedNode("T1"));
   }
   
   /**
    * Tests the tree in the wikipedia example 
    * <a href="http://en.wikipedia.org/wiki/Tree_traversal">http://en.wikipedia.org/wiki/Tree_traversal</a>:
    * <pre>
    *        F
    *    B       G
    * A    D       I
    *    C   E   H
    * </pre>
    * Depth-first
    * <ul>
    *    <li>Preorder traversal sequence: F, B, A, D, C, E, G, I, H (root, left, right)</li>
    *    <li>Inorder traversal sequence: A, B, C, D, E, F, G, H, I (left, root, right); note how this produces a sorted sequence</li>
    *    <li>Postorder traversal sequence: A, C, E, D, B, H, I, G, F (left, right, root)</li>
    * </ul>
    * Breadth-first
    * <ul>
    *    <li>Level-order traversal sequence: F, B, G, A, D, I, C, E, H</li>
    * </ul>
    */
   @Test
   public void testWikipediaTree() throws DebugException {
      // Create tree to test
      SEMemoryDebugTarget f = appendDebugTarget("F");
      SEMemoryThread b = appendThread(f, "B");
      appendStatement(f, b, b, "A");
      SEMemoryStatement d = appendStatement(f, b, b, "D");
      appendStatement(f, d, b, "C");
      appendStatement(f, d, b, "E");
      SEMemoryThread g = appendThread(f, "G");
      SEMemoryStatement i = appendStatement(f, g, g, "I");
      appendStatement(f, i, g, "H");
      // Test tree
      ExpectedNode[] expected_h = createExpectedNodes("H");
      ExpectedNode[] expected_i = createExpectedNodes(new String[] {"I"}, expected_h);
      ExpectedNode[] expected_ce = createExpectedNodes("C", "E");
      ExpectedNode[] expected_ad = createExpectedNodes(new String[] {"A", "D"}, null, expected_ce);
      ExpectedNode[] expected_bg = createExpectedNodes(new String[] {"B", "G"}, expected_ad, expected_i);
      assertTarget(f, createExpectedNode("F", expected_bg));
   }
   
   /**
    * Tests a tree with {@link ISENode} up to level three.
    */
   @Test
   public void testNodesThreeLevel() throws DebugException {
      // Create tree to test
      SEMemoryDebugTarget target = appendDebugTarget("target");
      SEMemoryThread thread1 = appendThread(target, "T1");
      appendStatement(target, thread1, thread1, "T1S1");
      SEMemoryStatement t1s2 = appendStatement(target, thread1, thread1, "T1S2");
      appendStatement(target, t1s2, thread1, "T1S2a");
      SEMemoryStatement t1s2b = appendStatement(target, t1s2, thread1, "T1S2b");
      appendStatement(target, t1s2b, thread1, "T1S2cI");
      appendStatement(target, t1s2, thread1, "T1S2c");
      SEMemoryStatement t1s3 = appendStatement(target, thread1, thread1, "T1S3");
      appendStatement(target, t1s3, thread1, "T1S3a");
      appendStatement(target, t1s3, thread1, "T1S3b");
      // Test tree
      ExpectedNode[] level2b1 = createExpectedNodes("T1S2cI");
      ExpectedNode[] level2b = createExpectedNodes(new String[] {"T1S2a", "T1S2b", "T1S2c"}, null, level2b1, null);
      ExpectedNode[] level2c = createExpectedNodes("T1S3a", "T1S3b");
      ExpectedNode[] level1 = createExpectedNodes(new String[] {"T1S1", "T1S2", "T1S3"}, null, level2b, level2c);
      ExpectedNode[] threads = createExpectedNodes(new String[] {"T1"}, level1);
      assertTarget(target, createExpectedNode("target", threads));
   }
   
   /**
    * Tests a tree with {@link ISENode} up to level two.
    */
   @Test
   public void testNodesTwoLevel() throws DebugException {
      // Create tree to test
      SEMemoryDebugTarget target = appendDebugTarget("target");
      SEMemoryThread thread1 = appendThread(target, "T1");
      appendStatement(target, thread1, thread1, "T1S1");
      SEMemoryStatement t1s2 = appendStatement(target, thread1, thread1, "T1S2");
      appendStatement(target, t1s2, thread1, "T1S2a");
      appendStatement(target, t1s2, thread1, "T1S2b");
      appendStatement(target, t1s2, thread1, "T1S2c");
      SEMemoryStatement t1s3 = appendStatement(target, thread1, thread1, "T1S3");
      appendStatement(target, t1s3, thread1, "T1S3a");
      appendStatement(target, t1s3, thread1, "T1S3b");
      // Test tree
      ExpectedNode[] level2b = createExpectedNodes("T1S2a", "T1S2b", "T1S2c");
      ExpectedNode[] level2c = createExpectedNodes("T1S3a", "T1S3b");
      ExpectedNode[] level1 = createExpectedNodes(new String[] {"T1S1", "T1S2", "T1S3"}, null, level2b, level2c);
      ExpectedNode[] threads = createExpectedNodes(new String[] {"T1"}, level1);
      ExpectedNode expected = createExpectedNode("target", threads);
      assertTarget(target, expected);
   }
   
   /**
    * Tests a tree with {@link ISENode} up to level one.
    */
   @Test
   public void testNodesOneLevel() throws DebugException {
      // Create tree to test
      SEMemoryDebugTarget target = appendDebugTarget("target");
      SEMemoryThread thread1 = appendThread(target, "T1");
      appendStatement(target, thread1, thread1, "T1S1");
      appendStatement(target, thread1, thread1, "T1S2");
      appendStatement(target, thread1, thread1, "T1S3");
      SEMemoryThread thread2 = appendThread(target, "T2");
      appendStatement(target, thread2, thread2, "T2S1");
      // Test tree
      ExpectedNode[] level1T1 = createExpectedNodes("T1S1", "T1S2", "T1S3");
      ExpectedNode[] level1T2 = createExpectedNodes("T2S1");
      ExpectedNode[] threads = createExpectedNodes(new String[] {"T1", "T2"}, level1T1, level1T2);
      ExpectedNode expected = createExpectedNode("target", threads);
      assertTarget(target, expected);
   }
   
   /**
    * Prints the tree starting at the given {@link ExpectedNode}.
    * @param root The root to print.
    */
   protected void printTree(ExpectedNode root) {
      printTree(root, 0);
   }

   /**
    * Prints the subtree starting at the given {@link ExpectedNode}.
    * @param node the {@link ExpectedNode} to print.
    * @param level The current level.
    */
   protected void printTree(ExpectedNode node, int level) {
      if (node != null) {
         for (int i = 0; i < level; i++) {
            System.out.print('\t');
         }
         System.out.println(node.expectedName);
         ExpectedNode[] children = node.getExpectedChildren();
         if (children != null) {
            for (ExpectedNode child : children) {
               printTree(child, level + 1);
            }
         }
      }
   }
   
   /**
    * Tests a tree which contains some {@link ISEThread}s but
    * no {@link ISENode}s.
    */
   @Test
   public void testThreadsOnly() throws DebugException {
      // Create tree to test
      SEMemoryDebugTarget target = appendDebugTarget("target");
      appendThread(target, "T1");
      appendThread(target, "T2");
      appendThread(target, "T3");
      // Test tree
      ExpectedNode[] threads = createExpectedNodes("T1", "T2", "T3");
      assertTarget(target, createExpectedNode("target", threads));
   }
   
   /**
    * Tests an empty {@link ISEDebugTarget}.
    */
   @Test
   public void testEmptyDebugTarget() throws DebugException {
      // Create tree to test
      SEMemoryDebugTarget target = appendDebugTarget("target");
      // Test tree
      assertTarget(target, createExpectedNode("target"));
   }
   
   /**
    * Creates a new {@link ISEIterator} to test.
    * @param start The start {@link ISEDebugElement}.
    * @return The created {@link ISEIterator}.
    * @throws DebugException Occurred Exception.
    */
   protected abstract ISEIterator createIterator(ISEDebugElement start) throws DebugException;
   
   /**
    * Makes sure that a {@link ISEIterator} which iterates over the given
    * {@link ISEDebugElement} returns nodes in defined order.
    * @param element The {@link ISEDebugElement} to iterate over.
    * @param root The expected root of the test oracle.
    * @throws DebugException Occurred Exception.
    */
   protected void assertTarget(ISEDebugElement element, 
                               ExpectedNode root) throws DebugException {
      ISEIterator iter = createIterator(element);
      assertNotNull(iter);
      assertExpectedNodes(iter, root, false);
      assertFalse(iter.hasNext());
   }
   
   /**
    * Makes sure that the nodes returned by the given {@link ISEIterator}
    * are equal to the defined model regarding the iteration order.
    * @param iter The {@link ISEIterator} to test.
    * @param root The expected root of the test oracle.
    * @param iterateOverSubtree Start new sub tree iteration at the current node?
    * @throws DebugException Occurred Exception.
    */
   protected abstract void assertExpectedNodes(ISEIterator iter, 
                                               ExpectedNode root,
                                               boolean iterateOverSubtree) throws DebugException;   
   
   /**
    * Forms the expected tree.
    * @author Martin Hentschel
    */
   protected static class ExpectedNode {
      /**
       * The expected name.
       */
      private String expectedName;
      
      /**
       * The expected children.
       */
      private ExpectedNode[] expectedChildren;

      /**
       * The parent {@link ExpectedNode}.
       */
      private ExpectedNode parent;
      
      /**
       * Constructor.
       * @param expectedName The expected name.
       */
      public ExpectedNode(String expectedName) {
         this.expectedName = expectedName;
      }

      /**
       * Constructor.
       * @param expectedName The expected name.
       * @param expectedChildren The expected children.
       */
      public ExpectedNode(String expectedName, ExpectedNode[] expectedChildren) {
         this.expectedName = expectedName;
         this.expectedChildren = expectedChildren;
      }
      
      /**
       * Returns the expected name.
       * @return The expected name.
       */
      public String getExpectedName() {
         return expectedName;
      }

      /**
       * Returns the expected children.
       * @return The expected children.
       */
      public ExpectedNode[] getExpectedChildren() {
         return expectedChildren;
      }

      /**
       * Returns the parent {@link ExpectedNode}.
       * @return The parent {@link ExpectedNode}.
       */
      public ExpectedNode getParent() {
         return parent;
      }

      /**
       * Sets the parent {@link ExpectedNode}.
       * @param parent The parent {@link ExpectedNode} to set.
       */
      public void setParent(ExpectedNode parent) {
         this.parent = parent;
      }
   }

   /**
    * Creates new {@link ExpectedNode}s with the given names and children.
    * @param names The given names.
    * @param children The given children.
    * @return The created {@link ExpectedNode}s.
    */
   protected ExpectedNode[] createExpectedNodes(String[] names, ExpectedNode[]... children) {
      assertEquals(names.length, children.length);
      List<ExpectedNode> result = new LinkedList<ExpectedNode>();
      for (int i = 0; i < names.length; i++) {
         ExpectedNode newNode = new ExpectedNode(names[i], children[i]);
         if (children[i] != null) {
            for (ExpectedNode child : children[i]) {
               child.setParent(newNode);
            }
         }
         result.add(newNode);
      }
      return result.toArray(new ExpectedNode[result.size()]);
   }
   
   /**
    * Creates a new {@link ExpectedNode} with the given name.
    * @param names The given name.
    * @param children The given children.
    * @return The created {@link ExpectedNode}.
    */
   protected ExpectedNode createExpectedNode(String name, ExpectedNode[] children) {
      ExpectedNode newNode = new ExpectedNode(name, children);
      if (children != null) {
         for (ExpectedNode child : children) {
            child.setParent(newNode);
         }
      }
      return newNode;
   }
   
   /**
    * Creates a new {@link ExpectedNode} with the given name.
    * @param names The given name.
    * @return The created {@link ExpectedNode}.
    */
   protected ExpectedNode createExpectedNode(String name) {
      return new ExpectedNode(name);
   }
   
   /**
    * Creates new {@link ExpectedNode}s with the given names.
    * @param names The given names.
    * @return The created {@link ExpectedNode}s.
    */
   protected ExpectedNode[] createExpectedNodes(String... names) {
      List<ExpectedNode> result = new LinkedList<ExpectedNode>();
      for (String name : names) {
         result.add(new ExpectedNode(name));
      }
      return result.toArray(new ExpectedNode[result.size()]);
   }

   /**
    * Instantiates a new {@link SEMemoryDebugTarget}.
    * @param name The name to use.
    * @return The instantiated {@link SEMemoryDebugTarget}.
    */
   protected static SEMemoryDebugTarget appendDebugTarget(String name) {
      SEMemoryDebugTarget target = new SEMemoryDebugTarget(null, false);
      target.setName(name);
      return target;
   }

   /**
    * Instantiates a new {@link SEMemoryThread} and adds it to the parent
    * {@link SEMemoryDebugTarget}.
    * @param target The parent {@link SEMemoryDebugTarget} to add to.
    * @param name The name to use.
    * @return The instantiated {@link SEMemoryThread}.
    */
   protected static SEMemoryThread appendThread(SEMemoryDebugTarget target, String name) {
      SEMemoryThread thread = new SEMemoryThread(target, false);
      thread.setName(name);
      target.addSymbolicThread(thread);
      return thread;
   }

   /**
    * Instantiates a new {@link SEMemoryStatement} and adds it to the parent
    * {@link ISEMemoryNode}.
    * @param target The parent {@link SEMemoryDebugTarget}.
    * @param parent The parent {@link ISEMemoryNode} to add to.
    * @param thread The parent {@link SEMemoryThread}.
    * @param name The name to use.
    * @return The instantiated {@link SEMemoryStatement}.
    */
   protected static SEMemoryStatement appendStatement(SEMemoryDebugTarget target, ISEMemoryNode parent, SEMemoryThread thread, String name) {
      SEMemoryStatement statement = new SEMemoryStatement(target, parent, thread);
      statement.setName(name);
      parent.addChild(statement);
      return statement;
   }
}