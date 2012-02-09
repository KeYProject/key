package org.key_project.key4eclipse.util.test.testcase;

import org.junit.Test;
import org.key_project.key4eclipse.util.java.thread.AbstractRunnableWithResult;
import org.key_project.key4eclipse.util.java.thread.IRunnableWithResult;

import junit.framework.TestCase;

/**
 * Tests for {@link AbstractRunnableWithResult}.
 * @author Martin Hentschel
 */
public class AbstractRunnableWithResultTest extends TestCase {
   /**
    * Tests {@link AbstractRunnableWithResult#getResult()} and
    * {@link AbstractRunnableWithResult#getException()}
    */
   @Test
   public void testGetResult() {
      final Exception e = new Exception();
      IRunnableWithResult<String> run = new AbstractRunnableWithResult<String>() {
         @Override
         public void run() {
            setResult("The result.");
            setException(e);
         }
      };
      assertNull(run.getResult());
      assertNull(run.getException());
      run.run();
      assertEquals("The result.", run.getResult());
      assertEquals(e, run.getException());
   }
}
