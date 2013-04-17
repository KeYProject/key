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

import java.io.File;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

import junit.framework.TestCase;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.junit.Test;

import de.hentschel.visualdbc.datasource.model.DSPackageManagement;
import de.hentschel.visualdbc.datasource.model.IDSDriver;
import de.hentschel.visualdbc.datasource.model.implementation.AbstractDSDriver;
import de.hentschel.visualdbc.datasource.test.util.TestDataSourceUtil;

/**
 * Contains test cases for {@link AbstractDSDriver}.
 * @author Martin Hentschel
 */
public class AbstractDSDriverTest extends TestCase {
   /**
    * Tests the management of {@link Boolean} values in the persistence management.
    */
   @Test
   public void testBooleanConnectionProperty() {
      IDSDriver driver = TestDataSourceUtil.getDummyDriver();
      testValueConvertion(driver, "theKey", Boolean.TRUE);
      testValueConvertion(driver, "theKey", Boolean.FALSE);
   }
   
   /**
    * Tests the management of {@link DSPackageManagement} values in the persistence management.
    */
   @Test
   public void testPackageManagementConnectionProperty() {
      IDSDriver driver = TestDataSourceUtil.getDummyDriver();
      testValueConvertion(driver, "theKey", DSPackageManagement.NO_PACKAGES);
      testValueConvertion(driver, "theKey", DSPackageManagement.FLAT_LIST);
      testValueConvertion(driver, "theKey", DSPackageManagement.HIERARCHY);
   }
   
   /**
    * Tests the management of {@link File} values in the persistence management.
    */
   @Test
   public void testFileConnectionProperty() {
      IDSDriver driver = TestDataSourceUtil.getDummyDriver();
      testValueConvertion(driver, "theKey", new File("temp"));
   }
   
   /**
    * Tests the management of {@link IPath} values in the persistence management.
    */
   @Test
   public void testPathConnectionProperty() {
      IDSDriver driver = TestDataSourceUtil.getDummyDriver();
      testValueConvertion(driver, "theKey", new Path("/projectA/myFolder"));
   }
   
   /**
    * Creates a initial map with the given key value pair. Then it is converted
    * to persistent properties and the original value is loaded from it.
    * In the end the given with the loaded value is compared.
    * @param driver The {@link IDSDriver} to use.
    * @param key The key to use.
    * @param value The value to test.
    */
   protected void testValueConvertion(IDSDriver driver, String key, Object value) {
      // Make sure that the driver is defined
      assertNotNull(driver);
      // Create initial map
      Map<String, Object> connectionSettings = new HashMap<String, Object>();
      connectionSettings.put(key, value);
      // Convert to persistent map
      Properties persistentProperties = driver.toPersistentProperties(connectionSettings);
      // Convert back to connectionSettings
      Map<String, Object> loadedProperties = driver.fromPersistentProperties(persistentProperties);
      assertTrue(loadedProperties.containsKey(key));
      assertEquals(value, loadedProperties.get(key));
   }
   
   /**
    * Tests the handling of an unsupported type in the persistent management.
    */
   @Test
   public void testUnsupportedTypeInToPersistentProperties() {
      IDSDriver driver = TestDataSourceUtil.getDummyDriver();
      // Create initial map
      Map<String, Object> connectionSettings = new HashMap<String, Object>();
      connectionSettings.put("theKey", new Object() {});
      // Convert to persistent map
      try {
         driver.toPersistentProperties(connectionSettings);
         fail();
      }
      catch (Exception e) {
         assertEquals("Unsupported connection value \"" + connectionSettings.get("theKey") + "\" in key \"theKey\".", e.getMessage());
      }
   }
   
   /**
    * Tests the handling of an unsupported type in the persistent management.
    */
   @Test
   public void testUnsupportedTypeInFromPersistentProperties() {
      IDSDriver driver = TestDataSourceUtil.getDummyDriver();
      // Create initial map
      Properties persistentProperties = new Properties();
      persistentProperties.setProperty("theKey", "xx");
      persistentProperties.setProperty("theKey" + AbstractDSDriver.TYPE_SUFFIX, "illegal.type");
      // Convert to persistent map
      try {
         driver.fromPersistentProperties(persistentProperties);
         fail();
      }
      catch (Exception e) {
         assertEquals("Unknown type \"illegal.type\" for key \"theKey\".", e.getMessage());
      }
   }
}