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

/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package de.hentschel.visualdbc.dbcmodel.tests;

import de.hentschel.visualdbc.dbcmodel.AbstractDbcTypeContainer;
import de.hentschel.visualdbc.dbcmodel.DbcClass;
import de.hentschel.visualdbc.dbcmodel.DbcEnum;
import de.hentschel.visualdbc.dbcmodel.DbcInterface;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;

/**
 * <!-- begin-user-doc -->
 * A test case for the model object '<em><b>Abstract Dbc Type Container</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following operations are tested:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcTypeContainer#getType(java.lang.String) <em>Get Type</em>}</li>
 * </ul>
 * </p>
 * @generated
 */
public abstract class AbstractDbcTypeContainerTest extends AbstractDbcProofContainerTest {

   /**
    * Constructs a new Abstract Dbc Type Container test case with the given name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public AbstractDbcTypeContainerTest(String name) {
      super(name);
   }

   /**
    * Returns the fixture for this Abstract Dbc Type Container test case.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected AbstractDbcTypeContainer getFixture() {
      return (AbstractDbcTypeContainer)fixture;
   }

   /**
    * Tests the '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcTypeContainer#getType(java.lang.String) <em>Get Type</em>}' operation.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcTypeContainer#getType(java.lang.String)
    * @generated NOT
    */
   public void testGetType__String() {
      // Create model
      AbstractDbcTypeContainer container = DbcmodelFactory.eINSTANCE.createDbcPackage();
      DbcClass classA = DbcmodelFactory.eINSTANCE.createDbcClass();
      classA.setName("classA");
      container.getTypes().add(classA);
      DbcClass classB = DbcmodelFactory.eINSTANCE.createDbcClass();
      classB.setName("classB");
      container.getTypes().add(classB);
      DbcClass classC = DbcmodelFactory.eINSTANCE.createDbcClass();
      classC.setName("classC");
      container.getTypes().add(classC);
      DbcClass classD = DbcmodelFactory.eINSTANCE.createDbcClass();
      classD.setName("classD");
      DbcInterface interfaceA = DbcmodelFactory.eINSTANCE.createDbcInterface();
      interfaceA.setName("interfaceA");
      container.getTypes().add(interfaceA);
      DbcInterface interfaceB = DbcmodelFactory.eINSTANCE.createDbcInterface();
      interfaceB.setName("interfaceB");
      container.getTypes().add(interfaceB);
      DbcInterface interfaceC = DbcmodelFactory.eINSTANCE.createDbcInterface();
      interfaceC.setName("interfaceC");
      container.getTypes().add(interfaceC);
      DbcInterface interfaceD = DbcmodelFactory.eINSTANCE.createDbcInterface();
      interfaceD.setName("interfaceD");
      DbcEnum enumA = DbcmodelFactory.eINSTANCE.createDbcEnum();
      enumA.setName("enumA");
      container.getTypes().add(enumA);
      DbcEnum enumB = DbcmodelFactory.eINSTANCE.createDbcEnum();
      enumB.setName("enumB");
      container.getTypes().add(enumB);
      DbcEnum enumC = DbcmodelFactory.eINSTANCE.createDbcEnum();
      enumC.setName("enumC");
      container.getTypes().add(enumC);
      DbcEnum enumD = DbcmodelFactory.eINSTANCE.createDbcEnum();
      enumD.setName("enumD");
      // Execute test
      assertEquals(classA, container.getType(classA.getName()));
      assertEquals(classB, container.getType(classB.getName()));
      assertEquals(classC, container.getType(classC.getName()));
      assertNull(container.getType(classD.getName()));
      assertEquals(interfaceA, container.getType(interfaceA.getName()));
      assertEquals(interfaceB, container.getType(interfaceB.getName()));
      assertEquals(interfaceC, container.getType(interfaceC.getName()));
      assertNull(container.getType(interfaceD.getName()));
      assertEquals(enumA, container.getType(enumA.getName()));
      assertEquals(enumB, container.getType(enumB.getName()));
      assertEquals(enumC, container.getType(enumC.getName()));
      assertNull(container.getType(enumD.getName()));
   }

} //AbstractDbcTypeContainerTest