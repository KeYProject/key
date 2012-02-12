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

package org.key_project.key4eclipse.starter.ui.test.testcase;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.key4eclipse.starter.ui.util.LogUtil;
import org.key_project.key4eclipse.util.eclipse.Logger;

/**
 * Contains tests for {@link LogUtil}
 * @author Martin Hentschel
 */
public class LogUtilTest extends TestCase {
   /**
    * Tests {@link LogUtil#getLogger()}
    */
   @Test
   public void testGetLogger() {
      Logger firstLogger = LogUtil.getLogger();
      assertNotNull(firstLogger);
      assertEquals("org.key_project.key4eclipse.starter.ui", firstLogger.getPlugInId());
      Logger secondLogger = LogUtil.getLogger();
      assertSame(firstLogger, secondLogger);
   }
}
