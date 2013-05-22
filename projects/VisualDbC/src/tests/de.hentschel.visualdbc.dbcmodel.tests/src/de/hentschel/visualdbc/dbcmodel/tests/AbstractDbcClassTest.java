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

import de.hentschel.visualdbc.dbcmodel.AbstractDbcClass;
import de.hentschel.visualdbc.dbcmodel.DbcConstructor;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;

/**
 * <!-- begin-user-doc -->
 * A test case for the model object '<em><b>Abstract Dbc Class</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following operations are tested:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcClass#getConstructor(java.lang.String) <em>Get Constructor</em>}</li>
 * </ul>
 * </p>
 * @generated
 */
public abstract class AbstractDbcClassTest extends AbstractDbcInterfaceTest {

   /**
    * Constructs a new Abstract Dbc Class test case with the given name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public AbstractDbcClassTest(String name) {
      super(name);
   }

   /**
    * Returns the fixture for this Abstract Dbc Class test case.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected AbstractDbcClass getFixture() {
      return (AbstractDbcClass)fixture;
   }

   /**
    * Tests the '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcClass#getConstructor(java.lang.String) <em>Get Constructor</em>}' operation.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcClass#getConstructor(java.lang.String)
    * @generated NOT
    */
   public void testGetConstructor__String() {
      // Create model
      AbstractDbcClass container = DbcmodelFactory.eINSTANCE.createDbcClass();
      DbcConstructor constructorA = DbcmodelFactory.eINSTANCE.createDbcConstructor();
      constructorA.setSignature("constructorA");
      container.getConstructors().add(constructorA);
      DbcConstructor constructorB = DbcmodelFactory.eINSTANCE.createDbcConstructor();
      constructorB.setSignature("constructorB");
      container.getConstructors().add(constructorB);
      DbcConstructor constructorC = DbcmodelFactory.eINSTANCE.createDbcConstructor();
      constructorC.setSignature("constructorC");
      container.getConstructors().add(constructorC);
      DbcConstructor constructorD = DbcmodelFactory.eINSTANCE.createDbcConstructor();
      constructorD.setSignature("constructorD");
      // Execute test
      assertEquals(constructorA, container.getConstructor(constructorA.getSignature()));
      assertEquals(constructorB, container.getConstructor(constructorB.getSignature()));
      assertEquals(constructorC, container.getConstructor(constructorC.getSignature()));
      assertNull(container.getConstructor(constructorD.getSignature()));
   }
} //AbstractDbcClassTest