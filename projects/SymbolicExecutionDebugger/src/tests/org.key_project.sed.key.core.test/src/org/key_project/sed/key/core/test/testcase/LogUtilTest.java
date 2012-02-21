package org.key_project.sed.key.core.test.testcase;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.sed.key.core.util.LogUtil;
import org.key_project.util.eclipse.Logger;

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
      assertEquals("org.key_project.sed.key.core", firstLogger.getPlugInId());
      Logger secondLogger = LogUtil.getLogger();
      assertSame(firstLogger, secondLogger);
   }
}
