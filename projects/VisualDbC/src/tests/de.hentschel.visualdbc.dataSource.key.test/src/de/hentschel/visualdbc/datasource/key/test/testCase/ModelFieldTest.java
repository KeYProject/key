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

import org.junit.Test;
import org.key_project.util.test.testcase.AbstractSetupTestCase;

import de.hentschel.visualdbc.datasource.key.model.KeyConnection;
import de.hentschel.visualdbc.datasource.key.test.util.TestKeyUtil;
import de.hentschel.visualdbc.datasource.model.DSPackageManagement;

/**
 * Tests the handling of model field clauses in a {@link KeyConnection}.
 * @author Martin Hentschel
 */
public class ModelFieldTest extends AbstractSetupTestCase {
   /**
    * Tests model field.
    */
   @Test
   public void testModelField_withoutAccessible() throws Exception {
      TestKeyUtil.testKeyConnection("ModelFieldTest_testModelField_withoutAccessible",
                                    "data/modelFieldTestWithoutAccessible",
                                    null,
                                    DSPackageManagement.FLAT_LIST,
                                    TestKeyUtil.createExpectedModelFieldTestModel(false));
   }
   
   /**
    * Tests model field.
    */
   @Test
   public void testModelField() throws Exception {
      TestKeyUtil.testKeyConnection("ModelFieldTest_testModelField",
                                    "data/modelFieldTest",
                                    null,
                                    DSPackageManagement.FLAT_LIST,
                                    TestKeyUtil.createExpectedModelFieldTestModel(true));
   }
}