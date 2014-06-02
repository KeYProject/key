/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
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

package de.hentschel.visualdbc.datasource.key.test.testCase;

import java.io.File;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.junit.Test;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.hentschel.visualdbc.datasource.key.model.KeyConnection;
import de.hentschel.visualdbc.datasource.key.test.Activator;
import de.hentschel.visualdbc.datasource.key.test.util.TestKeyUtil;
import de.hentschel.visualdbc.datasource.model.DSPackageManagement;
import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * Contains tests for {@link KeyConnection}.
 * @author Martin Hentschel
 */
public class KeyConnectionTest extends AbstractKeYTest {
   /**
    * Tests
    * {@link KeyConnection#connect(java.util.Map, boolean, org.eclipse.core.runtime.IProgressMonitor)},
    * {@link KeyConnection#isConnected()} and
    * {@link KeyConnection#disconnect()} by connecting to a valid location.
    */
   @Test
   public void testConnectionToValidLocation() throws Exception {
      testKeyConnection("KeyConnectionTest_testConnectionToValidLocation",
                        "data/quicktour/test",
                        "paycard",
                        DSPackageManagement.HIERARCHY,
                        Activator.PLUGIN_ID,
                        "data/quicktour/oracle/quicktour.dbc");
   }

   /**
    * Tests
    * {@link KeyConnection#connect(java.util.Map, boolean, org.eclipse.core.runtime.IProgressMonitor)},
    * {@link KeyConnection#isConnected()} and
    * {@link KeyConnection#disconnect()} by connecting to an invalid location.
    */
   @Test
   public void testConnectionToInvalidLocation() {
      try {
         // Create project and fill it with test data
         IProject project = TestUtilsUtil.createProject("KeyConnectionTest_testConnectionToInvalidLocation");
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/quicktour/test", project);
         IFolder guiFolder = project.getFolder("gui");
         assertNotNull(guiFolder);
         assertTrue(guiFolder.exists());
         // Open connection
         File location = ResourceUtil.getLocation(guiFolder); 
         assertNotNull(location);
         assertTrue(location.exists() && location.isDirectory());
         TestKeyUtil.createKeyConnection(location);
         fail();
      }
      catch (DSException e) {
         // Correct behavior
      }
      catch (Exception e) {
         e.printStackTrace();
         fail();
      }
   }
}