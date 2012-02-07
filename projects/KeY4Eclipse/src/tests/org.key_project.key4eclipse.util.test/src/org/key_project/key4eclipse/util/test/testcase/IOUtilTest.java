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

import java.io.ByteArrayInputStream;
import java.io.IOException;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.key4eclipse.util.java.IOUtil;


/**
 * Tests for {@link IOUtil}
 * @author Martin Hentschel
 */
public class IOUtilTest extends TestCase {
   /**
    * Tests {@link IOUtil#readFrom(java.io.InputStream)}
    */
   @Test
   public void testReadFrom() {
      try {
         doTestReadFrom(null);
         doTestReadFrom("One Line");
         doTestReadFrom("First Line\n\rSecond Line");
         doTestReadFrom("One Line\r");
         doTestReadFrom("One Line\n");
         doTestReadFrom("One Line\r\n");
         doTestReadFrom("One Line\n\r");
         StringBuffer sb = new StringBuffer();
         for (int i = 0; i < IOUtil.BUFFER_SIZE * 3; i++) {
            sb.append("A");
         }
         doTestReadFrom(sb.toString());
      }
      catch (IOException e) {
         e.printStackTrace();
         fail();
      }
   }
   
   /**
    * Executes the assertions for {@link #testReadFrom()}.
    * @param text The text to check.
    * @throws IOException Occurred Exception.
    */
   protected void doTestReadFrom(String text) throws IOException {
      if (text != null) {
         assertEquals(text, IOUtil.readFrom(new ByteArrayInputStream(text.getBytes())));
      }
      else {
         assertNull(IOUtil.readFrom(null));
      }
   }
}
