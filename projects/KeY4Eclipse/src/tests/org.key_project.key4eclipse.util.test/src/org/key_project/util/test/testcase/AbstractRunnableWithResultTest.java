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

package org.key_project.util.test.testcase;

import org.junit.Test;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;

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