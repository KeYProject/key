package org.key_project.sed.core.test.testcase;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.sed.core.util.SEDPreferenceUtil;
import org.key_project.sed.core.util.SEDPreferenceUtilInitializer;

/**
 * Tests for {@link SEDPreferenceUtilInitializer}.
 * @author Martin Hentschel
 */
public class SEDPreferenceUtilInitializerTest extends TestCase {
   /**
    * Tests the defined default values.
    */
   @Test
   public void testDefaultValues() {
      assertTrue(SEDPreferenceUtil.isDefaultShowCompactExecutionTree());
   }
}
