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

import org.junit.Test;
import org.key_project.util.java.StringUtil;
import org.key_project.util.java.XMLUtil;

import junit.framework.TestCase;

/**
 * Tests for {@link XMLUtil}.
 * @author Martin Hentschel
 */
public class XMLUtilTest extends TestCase {
   /**
    * Tests {@link XMLUtil#encodeText(String)}
    */
   @Test
   public void testEncodeText() {
      // Test null
      assertNull(XMLUtil.encodeText(null));
      // Test empty string
      assertEquals(StringUtil.EMPTY_STRING, XMLUtil.encodeText(StringUtil.EMPTY_STRING));
      // Text XML tags
      assertEquals("&lt;hello&gt;world&lt;/hello&gt;", XMLUtil.encodeText("<hello>world</hello>"));
      // Test XML attributes
      assertEquals("&lt;hello a=&quot;A&quot; b=&apos;B&apos;&gt;world&lt;/hello&gt;", XMLUtil.encodeText("<hello a=\"A\" b='B'>world</hello>"));
      // Test XML entities
      assertEquals("&lt;hello a=&quot;A&quot; b=&apos;B&apos;&gt;&amp;lt;world&amp;gt;&lt;/hello&gt;", XMLUtil.encodeText("<hello a=\"A\" b='B'>&lt;world&gt;</hello>"));
   }
}