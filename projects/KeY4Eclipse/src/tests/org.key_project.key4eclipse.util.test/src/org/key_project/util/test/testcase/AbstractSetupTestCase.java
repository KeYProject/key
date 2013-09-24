package org.key_project.util.test.testcase;

import org.junit.After;
import org.junit.Before;
import org.key_project.util.eclipse.setup.SetupStartup;
import org.key_project.util.test.util.TestUtilsUtil;

import junit.framework.TestCase;

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
