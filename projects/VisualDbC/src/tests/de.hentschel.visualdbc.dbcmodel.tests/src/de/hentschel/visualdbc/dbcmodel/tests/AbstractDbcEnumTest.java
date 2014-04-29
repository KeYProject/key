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

import de.hentschel.visualdbc.dbcmodel.AbstractDbcEnum;
import de.hentschel.visualdbc.dbcmodel.DbcEnum;
import de.hentschel.visualdbc.dbcmodel.DbcEnumLiteral;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;

/**
 * <!-- begin-user-doc -->
 * A test case for the model object '<em><b>Abstract Dbc Enum</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following operations are tested:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcEnum#getLiteral(java.lang.String) <em>Get Literal</em>}</li>
 * </ul>
 * </p>
 * @generated
 */
public abstract class AbstractDbcEnumTest extends AbstractDbcClassTest {

   /**
    * Constructs a new Abstract Dbc Enum test case with the given name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public AbstractDbcEnumTest(String name) {
      super(name);
   }

   /**
    * Returns the fixture for this Abstract Dbc Enum test case.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected AbstractDbcEnum getFixture() {
      return (AbstractDbcEnum)fixture;
   }

   /**
    * Tests the '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcEnum#getLiteral(java.lang.String) <em>Get Literal</em>}' operation.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcEnum#getLiteral(java.lang.String)
    * @generated NOT
    */
   public void testGetLiteral__String() {
      // Create model
      DbcEnum container = DbcmodelFactory.eINSTANCE.createDbcEnum();
      DbcEnumLiteral literalA = DbcmodelFactory.eINSTANCE.createDbcEnumLiteral();
      literalA.setName("literalA");
      container.getLiterals().add(literalA);
      DbcEnumLiteral literalB = DbcmodelFactory.eINSTANCE.createDbcEnumLiteral();
      literalB.setName("literalB");
      container.getLiterals().add(literalB);
      DbcEnumLiteral literalC = DbcmodelFactory.eINSTANCE.createDbcEnumLiteral();
      literalC.setName("literalC");
      container.getLiterals().add(literalC);
      DbcEnumLiteral literalD = DbcmodelFactory.eINSTANCE.createDbcEnumLiteral();
      literalD.setName("literalD");
      // Execute test
      assertEquals(literalA, container.getLiteral(literalA.getName()));
      assertEquals(literalB, container.getLiteral(literalB.getName()));
      assertEquals(literalC, container.getLiteral(literalC.getName()));
      assertNull(container.getLiteral(literalD.getName()));
   }

} //AbstractDbcEnumTest