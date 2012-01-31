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
import org.key_project.key4eclipse.util.java.StringUtil;

/**
 * Tests for {@link StringUtil}
 * @author Martin Hentschel
 */
public class StringUtilTest extends TestCase {
   /**
    * Tests {@link StringUtil#toLowerCase(String)}
    */
   @Test
   public void testToLowerCase() {
       assertNull(StringUtil.toLowerCase(null));
       assertEquals("aa", StringUtil.toLowerCase("AA"));
       assertEquals("aa", StringUtil.toLowerCase("aa"));
       assertEquals("aa", StringUtil.toLowerCase("Aa"));
       assertEquals("aa", StringUtil.toLowerCase("aA"));
   }

   /**
    * Tests {@link StringUtil#trim(String)}
    */
   @Test
   public void testTrim() {
      assertNull(StringUtil.trim(null));
      assertEquals("AA", StringUtil.trim("AA"));
      assertEquals("AA", StringUtil.trim(" AA "));
   }
   
   /**
    * Tests {@link StringUtil#isTrimmedEmpty(String)}
    */
   @Test
   public void testIsTrimmedEmpty() {
      assertTrue(StringUtil.isTrimmedEmpty(null));
      assertTrue(StringUtil.isTrimmedEmpty(""));
      assertTrue(StringUtil.isTrimmedEmpty(" "));
      assertFalse(StringUtil.isTrimmedEmpty(" A "));
   }

   /**
    * Tests {@link StringUtil#isEmpty(String)}
    */
   @Test
   public void testIsEmpty() {
      assertTrue(StringUtil.isEmpty(null));
      assertTrue(StringUtil.isEmpty(""));
      assertFalse(StringUtil.isEmpty(" "));
      assertFalse(StringUtil.isEmpty(" A "));
   }
}
