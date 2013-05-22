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

import java.lang.reflect.InvocationTargetException;

import junit.framework.TestCase;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.junit.Test;
import org.key_project.util.java.thread.AbstractRunnableWithProgressAndResult;
import org.key_project.util.java.thread.IRunnableWithProgressAndResult;

/**
 * Tests for {@link AbstractRunnableWithProgressAndResult}.
 * @author Martin Hentschel
 */
public class AbstractRunnableWithProgressAndResultTest extends TestCase {
    /**
     * Tests {@link AbstractRunnableWithProgressAndResult#getResult()}.
     */
    @Test
    public void testGetResult() throws InvocationTargetException, InterruptedException {
       IRunnableWithProgressAndResult<String> run = new AbstractRunnableWithProgressAndResult<String>() {
          @Override
          public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
              setResult("The result.");
          }
       };
       assertNull(run.getResult());
       run.run(new NullProgressMonitor());
       assertEquals("The result.", run.getResult());
    }
}