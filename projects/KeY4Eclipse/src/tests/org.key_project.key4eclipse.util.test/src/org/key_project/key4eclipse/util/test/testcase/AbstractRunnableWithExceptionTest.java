/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package org.key_project.key4eclipse.util.test.testcase;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.key4eclipse.util.java.thread.AbstractRunnableWithException;
import org.key_project.key4eclipse.util.java.thread.IRunnableWithException;

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
