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