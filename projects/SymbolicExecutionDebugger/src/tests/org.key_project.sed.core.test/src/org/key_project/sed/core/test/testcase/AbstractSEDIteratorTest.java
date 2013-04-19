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

package org.key_project.sed.core.test.testcase;

import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;

import org.eclipse.debug.core.DebugException;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.memory.ISEDMemoryDebugNode;
import org.key_project.sed.core.model.memory.SEDMemoryDebugTarget;
import org.key_project.sed.core.model.memory.SEDMemoryStatement;
import org.key_project.sed.core.model.memory.SEDMemoryThread;
import org.key_project.sed.core.util.ISEDIterator;

/**
 * Provides the basic methods a {@link TestCase} of an
 * {@link ISEDIterator} implementation needs.
 * @author Martin Hentschel
 */
public abstract class AbstractSEDIteratorTest extends TestCase {
   /**
    * Tests one empty {@link ISEDDebugNode} only for debugging purpose.
    */
   @Test
   public void testEmptyNode() throws DebugException {
      // Create tree to test
      SEDMemoryDebugTarget target = appendDebugTarget("target");
      SEDMemoryThread thread1 = appendThread(target, "T1");
      appendStatement(target, thread1, thread1, "T1S1");
      appendStatement(target, thread1, thread1, "T1S2");
      appendStatement(target, thread1, thread1, "T1S3");
      SEDMemoryThread thread2 = appendThread(target, "T2");
      SEDMemoryStatement t2s1 = appendStatement(target, thread2, thread2, "T2S1");
      // Test tree
      assertTarget(t2s1, createExpectedNode("T2S1"));
   }
   
   /**
    * Tests one empty {@link ISEDThread} only for debugging purpose.
    */
   @Test
   public void testEmptyThread() throws DebugException {
      // Create tree to test
      SEDMemoryDebugTarget target = appendDebugTarget("target");
      SEDMemoryThread t1 = appendThread(target, "T1");
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
      SEDMemoryDebugTarget f = appendDebugTarget("F");
      SEDMemoryThread b = appendThread(f, "B");
      appendStatement(f, b, b, "A");
      SEDMemoryStatement d = appendStatement(f, b, b, "D");
      appendStatement(f, d, b, "C");
      appendStatement(f, d, b, "E");
      SEDMemoryThread g = appendThread(f, "G");
      SEDMemoryStatement i = appendStatement(f, g, g, "I");
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
    * Tests a tree with {@link ISEDDebugNode} up to level three.
    */
   @Test
   public void testNodesThreeLevel() throws DebugException {
      // Create tree to test
      SEDMemoryDebugTarget target = appendDebugTarget("target");
      SEDMemoryThread thread1 = appendThread(target, "T1");
      appendStatement(target, thread1, thread1, "T1S1");
      SEDMemoryStatement t1s2 = appendStatement(target, thread1, thread1, "T1S2");
      appendStatement(target, t1s2, thread1, "T1S2a");
      SEDMemoryStatement t1s2b = appendStatement(target, t1s2, thread1, "T1S2b");
      appendStatement(target, t1s2b, thread1, "T1S2cI");
      appendStatement(target, t1s2, thread1, "T1S2c");
      SEDMemoryStatement t1s3 = appendStatement(target, thread1, thread1, "T1S3");
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
    * Tests a tree with {@link ISEDDebugNode} up to level two.
    */
   @Test
   public void testNodesTwoLevel() throws DebugException {
      // Create tree to test
      SEDMemoryDebugTarget target = appendDebugTarget("target");
      SEDMemoryThread thread1 = appendThread(target, "T1");
      appendStatement(target, thread1, thread1, "T1S1");
      SEDMemoryStatement t1s2 = appendStatement(target, thread1, thread1, "T1S2");
      appendStatement(target, t1s2, thread1, "T1S2a");
      appendStatement(target, t1s2, thread1, "T1S2b");
      appendStatement(target, t1s2, thread1, "T1S2c");
      SEDMemoryStatement t1s3 = appendStatement(target, thread1, thread1, "T1S3");
      appendStatement(target, t1s3, thread1, "T1S3a");
      appendStatement(target, t1s3, thread1, "T1S3b");
      // Test tree
      ExpectedNode[] level2b = createExpectedNodes("T1S2a", "T1S2b", "T1S2c");
      ExpectedNode[] level2c = createExpectedNodes("T1S3a", "T1S3b");
      ExpectedNode[] level1 = createExpectedNodes(new String[] {"T1S1", "T1S2", "T1S3"}, null, level2b, level2c);
      ExpectedNode[] threads = createExpectedNodes(new String[] {"T1"}, level1);
      assertTarget(target, createExpectedNode("target", threads));
   }
   
   /**
    * Tests a tree with {@link ISEDDebugNode} up to level one.
    */
   @Test
   public void testNodesOneLevel() throws DebugException {
      // Create tree to test
      SEDMemoryDebugTarget target = appendDebugTarget("target");
      SEDMemoryThread thread1 = appendThread(target, "T1");
      appendStatement(target, thread1, thread1, "T1S1");
      appendStatement(target, thread1, thread1, "T1S2");
      appendStatement(target, thread1, thread1, "T1S3");
      SEDMemoryThread thread2 = appendThread(target, "T2");
      appendStatement(target, thread2, thread2, "T2S1");
      // Test tree
      ExpectedNode[] level1T1 = createExpectedNodes("T1S1", "T1S2", "T1S3");
      ExpectedNode[] level1T2 = createExpectedNodes("T2S1");
      ExpectedNode[] threads = createExpectedNodes(new String[] {"T1", "T2"}, level1T1, level1T2);
      assertTarget(target, createExpectedNode("target", threads));
   }

   /**
    * Tests a tree which contains some {@link ISEDThread}s but
    * no {@link ISEDDebugNode}s.
    */
   @Test
   public void testThreadsOnly() throws DebugException {
      // Create tree to test
      SEDMemoryDebugTarget target = appendDebugTarget("target");
      appendThread(target, "T1");
      appendThread(target, "T2");
      appendThread(target, "T3");
      // Test tree
      ExpectedNode[] threads = createExpectedNodes("T1", "T2", "T3");
      assertTarget(target, createExpectedNode("target", threads));
   }
   
   /**
    * Tests an empty {@link ISEDDebugTarget}.
    */
   @Test
   public void testEmptyDebugTarget() throws DebugException {
      // Create tree to test
      SEDMemoryDebugTarget target = appendDebugTarget("target");
      // Test tree
      assertTarget(target, createExpectedNode("target"));
   }
   
   /**
    * Creates a new {@link ISEDIterator} to test.
    * @param start The start {@link ISEDDebugElement}.
    * @return The created {@link ISEDIterator}.
    * @throws DebugException Occurred Exception.
    */
   protected abstract ISEDIterator createIterator(ISEDDebugElement start) throws DebugException;
   
   /**
    * Makes sure that a {@link ISEDIterator} which iterates over the given
    * {@link ISEDDebugElement} returns nodes in defined order.
    * @param element The {@link ISEDDebugElement} to iterate over.
    * @param root The expected root of the test oracle.
    * @throws DebugException Occurred Exception.
    */
   protected void assertTarget(ISEDDebugElement element, 
                               ExpectedNode root) throws DebugException {
      ISEDIterator iter = createIterator(element);
      assertNotNull(iter);
      assertExpectedNodes(iter, root, false);
      assertFalse(iter.hasNext());
   }
   
   /**
    * Makes sure that the nodes returned by the given {@link ISEDIterator}
    * are equal to the defined model regarding the iteration order.
    * @param iter The {@link ISEDIterator} to test.
    * @param root The expected root of the test oracle.
    * @param iterateOverSubtree Start new sub tree iteration at the current node?
    * @throws DebugException Occurred Exception.
    */
   protected abstract void assertExpectedNodes(ISEDIterator iter, 
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
    * Instantiates a new {@link SEDMemoryDebugTarget}.
    * @param name The name to use.
    * @return The instantiated {@link SEDMemoryDebugTarget}.
    */
   protected static SEDMemoryDebugTarget appendDebugTarget(String name) {
      SEDMemoryDebugTarget target = new SEDMemoryDebugTarget(null);
      target.setName(name);
      return target;
   }

   /**
    * Instantiates a new {@link SEDMemoryThread} and adds it to the parent
    * {@link SEDMemoryDebugTarget}.
    * @param target The parent {@link SEDMemoryDebugTarget} to add to.
    * @param name The name to use.
    * @return The instantiated {@link SEDMemoryThread}.
    */
   protected static SEDMemoryThread appendThread(SEDMemoryDebugTarget target, String name) {
      SEDMemoryThread thread = new SEDMemoryThread(target);
      thread.setName(name);
      target.addSymbolicThread(thread);
      return thread;
   }

   /**
    * Instantiates a new {@link SEDMemoryStatement} and adds it to the parent
    * {@link ISEDMemoryDebugNode}.
    * @param target The parent {@link SEDMemoryDebugTarget}.
    * @param parent The parent {@link ISEDMemoryDebugNode} to add to.
    * @param thread The parent {@link SEDMemoryThread}.
    * @param name The name to use.
    * @return The instantiated {@link SEDMemoryStatement}.
    */
   protected static SEDMemoryStatement appendStatement(SEDMemoryDebugTarget target, ISEDMemoryDebugNode parent, SEDMemoryThread thread, String name) {
      SEDMemoryStatement statement = new SEDMemoryStatement(target, parent, thread);
      statement.setName(name);
      parent.addChild(statement);
      return statement;
   }
}