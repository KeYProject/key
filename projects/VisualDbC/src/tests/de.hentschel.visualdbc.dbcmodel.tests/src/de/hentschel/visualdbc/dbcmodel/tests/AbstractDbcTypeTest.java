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

import de.hentschel.visualdbc.dbcmodel.AbstractDbcType;
import de.hentschel.visualdbc.dbcmodel.DbcAxiom;
import de.hentschel.visualdbc.dbcmodel.DbcClass;
import de.hentschel.visualdbc.dbcmodel.DbcInvariant;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;

/**
 * <!-- begin-user-doc -->
 * A test case for the model object '<em><b>Abstract Dbc Type</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following operations are tested:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcType#getInvariant(java.lang.String) <em>Get Invariant</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcType#getAxiom(java.lang.String) <em>Get Axiom</em>}</li>
 * </ul>
 * </p>
 * @generated
 */
public abstract class AbstractDbcTypeTest extends AbstractDbcTypeContainerTest {

   /**
    * Constructs a new Abstract Dbc Type test case with the given name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public AbstractDbcTypeTest(String name) {
      super(name);
   }

   /**
    * Returns the fixture for this Abstract Dbc Type test case.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected AbstractDbcType getFixture() {
      return (AbstractDbcType)fixture;
   }

   /**
    * Tests the '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcType#getInvariant(java.lang.String) <em>Get Invariant</em>}' operation.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcType#getInvariant(java.lang.String)
    * @generated NOT
    */
   public void testGetInvariant__String() {
      // Create model
      DbcClass container = DbcmodelFactory.eINSTANCE.createDbcClass();
      DbcInvariant invariantA = DbcmodelFactory.eINSTANCE.createDbcInvariant();
      invariantA.setCondition("invariantA");
      container.getInvariants().add(invariantA);
      DbcInvariant invariantB = DbcmodelFactory.eINSTANCE.createDbcInvariant();
      invariantB.setCondition("invariantB");
      container.getInvariants().add(invariantB);
      DbcInvariant invariantC = DbcmodelFactory.eINSTANCE.createDbcInvariant();
      invariantC.setCondition("invariantC");
      container.getInvariants().add(invariantC);
      DbcInvariant invariantD = DbcmodelFactory.eINSTANCE.createDbcInvariant();
      invariantD.setCondition("invariantD");
      // Execute test
      assertEquals(invariantA, container.getInvariant(invariantA.getCondition()));
      assertEquals(invariantB, container.getInvariant(invariantB.getCondition()));
      assertEquals(invariantC, container.getInvariant(invariantC.getCondition()));
      assertNull(container.getInvariant(invariantD.getCondition()));
   }

   /**
    * Tests the '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcType#getAxiom(java.lang.String) <em>Get Axiom</em>}' operation.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcType#getAxiom(java.lang.String)
    * @generated NOT
    */
    public void testGetAxiom__String() {
       // Create model
       DbcClass container = DbcmodelFactory.eINSTANCE.createDbcClass();
       DbcAxiom axiomA = DbcmodelFactory.eINSTANCE.createDbcAxiom();
       axiomA.setDefinition("axiomA");
       container.getAxioms().add(axiomA);
       DbcAxiom axiomB = DbcmodelFactory.eINSTANCE.createDbcAxiom();
       axiomB.setDefinition("axiomB");
       container.getAxioms().add(axiomB);
       DbcAxiom axiomC = DbcmodelFactory.eINSTANCE.createDbcAxiom();
       axiomC.setDefinition("axiomC");
       container.getAxioms().add(axiomC);
       DbcAxiom axiomD = DbcmodelFactory.eINSTANCE.createDbcAxiom();
       axiomD.setDefinition("axiomD");
       // Execute test
       assertEquals(axiomA, container.getAxiom(axiomA.getDefinition()));
       assertEquals(axiomB, container.getAxiom(axiomB.getDefinition()));
       assertEquals(axiomC, container.getAxiom(axiomC.getDefinition()));
       assertNull(container.getAxiom(axiomD.getDefinition()));
   }

} //AbstractDbcTypeTest