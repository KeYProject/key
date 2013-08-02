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

/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package de.hentschel.visualdbc.dbcmodel.tests;

import de.hentschel.visualdbc.dbcmodel.AbstractDbCContainer;
import de.hentschel.visualdbc.dbcmodel.DbcPackage;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;

/**
 * <!-- begin-user-doc -->
 * A test case for the model object '<em><b>Abstract Db CContainer</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following operations are tested:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.AbstractDbCContainer#getPackage(java.lang.String) <em>Get Package</em>}</li>
 * </ul>
 * </p>
 * @generated
 */
public abstract class AbstractDbCContainerTest extends AbstractDbcTypeContainerTest {

   /**
    * Constructs a new Abstract Db CContainer test case with the given name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public AbstractDbCContainerTest(String name) {
      super(name);
   }

   /**
    * Returns the fixture for this Abstract Db CContainer test case.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected AbstractDbCContainer getFixture() {
      return (AbstractDbCContainer)fixture;
   }

   /**
    * Tests the '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbCContainer#getPackage(java.lang.String) <em>Get Package</em>}' operation.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbCContainer#getPackage(java.lang.String)
    * @generated NOT
    */
   public void testGetPackage__String() {
      // Create model
      AbstractDbCContainer container = DbcmodelFactory.eINSTANCE.createDbcPackage();
      DbcPackage packageA = DbcmodelFactory.eINSTANCE.createDbcPackage();
      packageA.setName("packageA");
      container.getPackages().add(packageA);
      DbcPackage packageB = DbcmodelFactory.eINSTANCE.createDbcPackage();
      packageB.setName("packageB");
      container.getPackages().add(packageB);
      DbcPackage packageC = DbcmodelFactory.eINSTANCE.createDbcPackage();
      packageC.setName("packageC");
      container.getPackages().add(packageC);
      DbcPackage packageD = DbcmodelFactory.eINSTANCE.createDbcPackage();
      packageD.setName("packageD");
      // Execute test
      assertEquals(packageA, container.getPackage(packageA.getName()));
      assertEquals(packageB, container.getPackage(packageB.getName()));
      assertEquals(packageC, container.getPackage(packageC.getName()));
      assertNull(container.getPackage(packageD.getName()));
   }

} //AbstractDbCContainerTest