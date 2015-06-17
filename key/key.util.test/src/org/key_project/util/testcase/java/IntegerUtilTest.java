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

package org.key_project.util.testcase.java;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.util.java.IntegerUtil;

/**
 * Tests for {@link IntegerUtil}
 * @author Martin Hentschel
 */
public class IntegerUtilTest extends TestCase {
   /**
    * Tests {@link IntegerUtil#factorial(int)}.
    */
   @Test
   public void testFactorial() {
      assertEquals(-1, IntegerUtil.factorial(-3));
      assertEquals(-1, IntegerUtil.factorial(-2));
      assertEquals(-1, IntegerUtil.factorial(-1));
      assertEquals(1, IntegerUtil.factorial(0));
      assertEquals(1, IntegerUtil.factorial(1));
      assertEquals(2, IntegerUtil.factorial(2));
      assertEquals(6, IntegerUtil.factorial(3));
      assertEquals(24, IntegerUtil.factorial(4));
      assertEquals(120, IntegerUtil.factorial(5));
   }
}