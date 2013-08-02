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

package de.hentschel.visualdbc.datasource.key.test.testCase;

import junit.framework.TestCase;

import org.junit.Test;

import de.hentschel.visualdbc.datasource.key.model.KeyConnection;
import de.hentschel.visualdbc.datasource.key.test.util.TestKeyUtil;
import de.hentschel.visualdbc.datasource.model.DSPackageManagement;

/**
 * Tests the handling of packages in a {@link KeyConnection}.
 * @author Martin Hentschel
 */
public class PackageTest extends TestCase {
   /**
    * Tests packages with management {@link DSPackageManagement#NO_PACKAGES}
    */
   @Test
   public void testPackageManagement_noPackages() throws Exception {
      TestKeyUtil.testKeyConnection("testPackageManagement_noPackages",
                                    "data/packageTest",
                                    null,
                                    DSPackageManagement.NO_PACKAGES,
                                    TestKeyUtil.createExpectedPackageTestModel_NoPackages());
   }

   /**
    * Tests packages with management {@link DSPackageManagement#FLAT_LIST}
    */
   @Test
   public void testPackageManagement_flatList() throws Exception {
      TestKeyUtil.testKeyConnection("testPackageManagement_flatList",
                                    "data/packageTest",
                                    null,
                                    DSPackageManagement.FLAT_LIST,
                                    TestKeyUtil.createExpectedPackageTestModel_FlatList());
   }

   /**
    * Tests packages with management {@link DSPackageManagement#HIERARCHY}
    */
   @Test
   public void testPackageManagement_hierarchy() throws Exception {
      TestKeyUtil.testKeyConnection("testPackageManagement_hierarchy",
                                    "data/packageTest",
                                    null,
                                    DSPackageManagement.HIERARCHY,
                                    TestKeyUtil.createExpectedPackageTestModel_Hierarchy());
   }
}