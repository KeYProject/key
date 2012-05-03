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
import org.key_project.sed.core.util.SEDIterator;

/**
 * Contains tests for {@link SEDIterator}.
 * @author Martin Hentschel
 */
public class SEDIteratorTest extends TestCase {
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
      assertTarget(target, createExpectedNodes(new String[] {"target"}, threads));
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
      assertTarget(target, createExpectedNodes(new String[] {"target"}, threads));
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
      assertTarget(target, createExpectedNodes(new String[] {"target"}, threads));
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
      assertTarget(target, createExpectedNodes(new String[] {"target"}, threads));
   }
   
   /**
    * Tests an empty {@link ISEDDebugTarget}.
    */
   @Test
   public void testEmptyDebugTarget() throws DebugException {
      // Create tree to test
      SEDMemoryDebugTarget target = appendDebugTarget("target");
      // Test tree
      assertTarget(target, createExpectedNodes("target"));
   }
   
   /**
    * Makes sure that a {@link SEDIterator} which iterates over the given
    * {@link ISEDDebugElement} returns nodes in preorder iteration over the
    * expected trees.
    * @param element The {@link ISEDDebugElement} to iterate over.
    * @param expectedRoots The expected values.
    * @throws DebugException Occurred Exception.
    */
   protected void assertTarget(ISEDDebugElement element, 
                               ExpectedNode[] expectedRoots) throws DebugException {
      SEDIterator iter = new SEDIterator(element);
      assertExpectedNodes(iter, expectedRoots, false);
      assertFalse(iter.hasNext());
   }
   
   /**
    * Makes sure that the nodes returned by the given {@link SEDIterator}
    * are equal to the defined model.
    * @param iter The {@link SEDIterator} to test.
    * @param expectedRoots The expected model.
    * @param iterateOverSubtree Start new sub tree iteration at the current node?
    * @throws DebugException Occurred Exception.
    */
   protected void assertExpectedNodes(SEDIterator iter, 
                                      ExpectedNode[] expectedRoots,
                                      boolean iterateOverSubtree) throws DebugException {
      if (expectedRoots != null) {
         assertNotNull(iter);
         for (ExpectedNode node : expectedRoots) {
            assertTrue(iter.hasNext());
            ISEDDebugElement next = iter.next();
            assertNotNull(next);
            if (next instanceof ISEDDebugTarget) {
               assertEquals(node.getExpectedName(), ((ISEDDebugTarget)next).getName());
            }
            else if (next instanceof ISEDDebugNode) {
               assertEquals(node.getExpectedName(), ((ISEDDebugNode)next).getName());
            }
            else {
               fail("Unknown element \"" + next + "\".");
            }
            if (iterateOverSubtree) {
               assertTarget(next, new ExpectedNode[] {node});
            }
            assertExpectedNodes(iter, node.getExpectedChildren(), true);
         }
      }
   }
   
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
         result.add(new ExpectedNode(names[i], children[i]));
      }
      return result.toArray(new ExpectedNode[result.size()]);
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
