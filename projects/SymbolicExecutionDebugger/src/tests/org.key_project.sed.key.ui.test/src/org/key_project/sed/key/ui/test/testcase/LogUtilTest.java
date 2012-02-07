package org.key_project.sed.key.ui.test.testcase;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.key4eclipse.util.eclipse.Logger;
import org.key_project.sed.key.ui.util.LogUtil;

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
      assertEquals("org.key_project.sed.key.ui", firstLogger.getPlugInId());
      Logger secondLogger = LogUtil.getLogger();
      assertSame(firstLogger, secondLogger);
   }
}
