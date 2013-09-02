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

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.sed.core.util.SEDPreferenceUtil;
import org.key_project.sed.core.util.SEDPreferenceUtilInitializer;
import org.key_project.util.test.testcase.AbstractSetupTestCase;

/**
 * Tests for {@link SEDPreferenceUtilInitializer}.
 * @author Martin Hentschel
 */
public class SEDPreferenceUtilInitializerTest extends AbstractSetupTestCase {
   /**
    * Tests the defined default values.
    */
   @Test
   public void testDefaultValues() {
      assertTrue(SEDPreferenceUtil.isDefaultShowCompactExecutionTree());
   }
}