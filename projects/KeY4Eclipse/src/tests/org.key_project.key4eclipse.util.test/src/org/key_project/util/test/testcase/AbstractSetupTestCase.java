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

import junit.framework.TestCase;

import org.junit.After;
import org.junit.Before;
import org.key_project.util.eclipse.setup.SetupStartup;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Provides the basic functionality for test cases which requires
 * that the {@link SetupStartup} is completed.
 * @author Martin Hentschel
 */
public abstract class AbstractSetupTestCase extends TestCase {
   /**
    * {@inheritDoc}
    */
   @Before
   @Override
   public void setUp() throws Exception {
      super.setUp();
      TestUtilsUtil.waitUntilWorkspaceInitialized();
   }

   /**
    * {@inheritDoc}
    */
   @After
   @Override
   public void tearDown() throws Exception {
      super.tearDown();
   }
}