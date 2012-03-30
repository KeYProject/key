package org.key_project.sed.core.test.testcase;

import junit.framework.TestCase;

import org.eclipse.debug.core.DebugException;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
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
    * Tests an empty {@link ISEDDebugTarget}.
    */
   @Test
   public void testNodesThreeLevel() throws DebugException {
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
      assertTarget(target, "target", "T1", "T1S1", "T1S2", "T1S2a", "T1S2b", "T1S2cI", "T1S2c", "T1S3", "T1S3a", "T1S3b");
   }
   
   /**
    * Tests an empty {@link ISEDDebugTarget}.
    */
   @Test
   public void testNodesTwoLevel() throws DebugException {
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
      assertTarget(target, "target", "T1", "T1S1", "T1S2", "T1S2a", "T1S2b", "T1S2c", "T1S3", "T1S3a", "T1S3b");
   }
   
   /**
    * Tests an empty {@link ISEDDebugTarget}.
    */
   @Test
   public void testNodesOneLevel() throws DebugException {
      SEDMemoryDebugTarget target = appendDebugTarget("target");
      SEDMemoryThread thread1 = appendThread(target, "T1");
      appendStatement(target, thread1, thread1, "T1S1");
      appendStatement(target, thread1, thread1, "T1S2");
      appendStatement(target, thread1, thread1, "T1S3");
      SEDMemoryThread thread2 = appendThread(target, "T2");
      appendStatement(target, thread2, thread2, "T2S1");
      assertTarget(target, "target", "T1", "T1S1", "T1S2", "T1S3", "T2", "T2S1");
   }

   /**
    * Tests an empty {@link ISEDDebugTarget}.
    */
   @Test
   public void testThreadsOnly() throws DebugException {
      SEDMemoryDebugTarget target = appendDebugTarget("target");
      appendThread(target, "T1");
      appendThread(target, "T2");
      appendThread(target, "T3");
      assertTarget(target, "target", "T1", "T2", "T3");
   }
   
   /**
    * Tests an empty {@link ISEDDebugTarget}.
    */
   @Test
   public void testEmptyDebugTarget() throws DebugException {
      SEDMemoryDebugTarget target = appendDebugTarget("target");
      assertTarget(target, "target");
   }
   
   /**
    * Makes sure that the given {@link ISEDDebugTarget} contains
    * elements which matches the given names in exactly that order.
    * @param target The {@link ISEDDebugTarget} to test.
    * @param expectedNames The expected elements names.
    * @throws DebugException Occurred Exception.
    */
   protected void assertTarget(ISEDDebugTarget target, String... expectedNames) throws DebugException {
      assertNotNull(target);
      SEDIterator iter = new SEDIterator(target);
      for (String name : expectedNames) {
         assertTrue(iter.hasNext());
         ISEDDebugElement next = iter.next();
         assertNotNull(next);
         if (next instanceof ISEDDebugTarget) {
            assertEquals(name, ((ISEDDebugTarget)next).getName());
         }
         else if (next instanceof ISEDDebugNode) {
            assertEquals(name, ((ISEDDebugNode)next).getName());
         }
         else {
            fail("Unknown element \"" + next + "\".");
         }
      }
      assertFalse(iter.hasNext());
      assertNull(iter.next());
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
