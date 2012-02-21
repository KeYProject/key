package org.key_project.util.test.testcase;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.util.java.thread.AbstractRunnableWithException;
import org.key_project.util.java.thread.IRunnableWithException;

/**
 * Tests for {@link AbstractRunnableWithException}.
 * @author Martin Hentschel
 */
public class AbstractRunnableWithExceptionTest extends TestCase {
   /**
    * Tests {@link AbstractRunnableWithException#getException()}
    */
   @Test
   public void testGetResult() {
      final Exception e = new Exception();
      IRunnableWithException run = new AbstractRunnableWithException() {
         @Override
         public void run() {
            setException(e);
         }
      };
      assertNull(run.getException());
      run.run();
      assertEquals(e, run.getException());
   }
}
