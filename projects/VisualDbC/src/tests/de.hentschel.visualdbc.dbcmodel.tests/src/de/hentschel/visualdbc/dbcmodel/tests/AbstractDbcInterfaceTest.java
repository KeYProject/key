/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package de.hentschel.visualdbc.dbcmodel.tests;

import de.hentschel.visualdbc.dbcmodel.AbstractDbcInterface;
import de.hentschel.visualdbc.dbcmodel.DbcMethod;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;

/**
 * <!-- begin-user-doc -->
 * A test case for the model object '<em><b>Abstract Dbc Interface</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following operations are tested:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcInterface#getMethod(java.lang.String) <em>Get Method</em>}</li>
 * </ul>
 * </p>
 * @generated
 */
public abstract class AbstractDbcInterfaceTest extends AbstractDbcTypeTest {

   /**
    * Constructs a new Abstract Dbc Interface test case with the given name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public AbstractDbcInterfaceTest(String name) {
      super(name);
   }

   /**
    * Returns the fixture for this Abstract Dbc Interface test case.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected AbstractDbcInterface getFixture() {
      return (AbstractDbcInterface)fixture;
   }

   /**
    * Tests the '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcInterface#getMethod(java.lang.String) <em>Get Method</em>}' operation.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcInterface#getMethod(java.lang.String)
    * @generated NOT
    */
   public void testGetMethod__String() {
      // Create model
      AbstractDbcInterface container = DbcmodelFactory.eINSTANCE.createDbcInterface();
      DbcMethod methodA = DbcmodelFactory.eINSTANCE.createDbcMethod();
      methodA.setSignature("constructorA");
      container.getMethods().add(methodA);
      DbcMethod methodB = DbcmodelFactory.eINSTANCE.createDbcMethod();
      methodB.setSignature("methodB");
      container.getMethods().add(methodB);
      DbcMethod methodC = DbcmodelFactory.eINSTANCE.createDbcMethod();
      methodC.setSignature("methodC");
      container.getMethods().add(methodC);
      DbcMethod methodD = DbcmodelFactory.eINSTANCE.createDbcMethod();
      methodA.setSignature("methodD");
      // Execute test
      assertEquals(methodA, container.getMethod(methodA.getSignature()));
      assertEquals(methodB, container.getMethod(methodB.getSignature()));
      assertEquals(methodC, container.getMethod(methodC.getSignature()));
      assertNull(container.getMethod(methodD.getSignature()));
   }

} //AbstractDbcInterfaceTest
