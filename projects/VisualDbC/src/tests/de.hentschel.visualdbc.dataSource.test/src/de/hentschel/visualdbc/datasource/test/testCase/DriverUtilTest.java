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

package de.hentschel.visualdbc.datasource.test.testCase;

import junit.framework.TestCase;

import org.junit.Test;

import de.hentschel.visualdbc.datasource.model.IDSDriver;
import de.hentschel.visualdbc.datasource.test.dummyModel.DummyModelDriver;
import de.hentschel.visualdbc.datasource.util.DriverUtil;

/**
 * Tests for {@link DriverUtil}
 * @author Martin Hentschel
 */
public class DriverUtilTest extends TestCase {
   /**
    * Tests for {@link DriverUtil#getDriver(String)}
    */
   @Test
   public void testGetDriver() {
      // Test invalid values
      assertNull(DriverUtil.getDriver(null));
      assertNull(DriverUtil.getDriver("INVALID_ID"));
      // Test dummy driver
      IDSDriver driver = DriverUtil.getDriver(DummyModelDriver.ID);
      assertNotNull(driver);
      assertEquals(DummyModelDriver.ID, driver.getId());
      // Test dummy driver again to make sure that the same instance is returned
      IDSDriver driverAgain = DriverUtil.getDriver(DummyModelDriver.ID);
      assertNotNull(driverAgain);
      assertEquals(DummyModelDriver.ID, driverAgain.getId());
      assertSame(driver, driverAgain);
   }
}