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

import junit.framework.TestCase;
import junit.textui.TestRunner;
import de.hentschel.visualdbc.dbcmodel.DbCAxiomContract;
import de.hentschel.visualdbc.dbcmodel.DbcAxiom;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;

/**
 * <!-- begin-user-doc -->
 * A test case for the model object '<em><b>Dbc Axiom</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following operations are tested:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcAxiom#getAxiomContract(java.lang.String, java.lang.String) <em>Get Axiom Contract</em>}</li>
 * </ul>
 * </p>
 * @generated
 */
public class DbcAxiomTest extends TestCase {

    /**
    * The fixture for this Dbc Axiom test case.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    */
    protected DbcAxiom fixture = null;

    /**
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    */
    public static void main(String[] args) {
      TestRunner.run(DbcAxiomTest.class);
   }

    /**
    * Constructs a new Dbc Axiom test case with the given name.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    */
    public DbcAxiomTest(String name) {
      super(name);
   }

    /**
    * Sets the fixture for this Dbc Axiom test case.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    */
    protected void setFixture(DbcAxiom fixture) {
      this.fixture = fixture;
   }

    /**
    * Returns the fixture for this Dbc Axiom test case.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    */
    protected DbcAxiom getFixture() {
      return fixture;
   }

    /**
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @see junit.framework.TestCase#setUp()
    * @generated
    */
    @Override
    protected void setUp() throws Exception {
      setFixture(DbcmodelFactory.eINSTANCE.createDbcAxiom());
   }

    /**
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @see junit.framework.TestCase#tearDown()
    * @generated
    */
    @Override
    protected void tearDown() throws Exception {
      setFixture(null);
   }

   /**
    * Tests the '{@link de.hentschel.visualdbc.dbcmodel.DbcAxiom#getAxiomContract(java.lang.String, java.lang.String) <em>Get Axiom Contract</em>}' operation.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.DbcAxiom#getAxiomContract(java.lang.String, java.lang.String)
    * @generated NOT
    */
   public void testGetAxiomContract__String_String() {
      // Create model
      DbcAxiom container = DbcmodelFactory.eINSTANCE.createDbcAxiom();
      DbCAxiomContract contractA = DbcmodelFactory.eINSTANCE.createDbCAxiomContract();
      contractA.setName("contractA");
      contractA.setPre("contractAPre");
      contractA.setDep("contractAPost");
      container.getAxiomContracts().add(contractA);
      DbCAxiomContract contractB = DbcmodelFactory.eINSTANCE.createDbCAxiomContract();
      contractB.setName("contractB");
      contractB.setPre("contractBPre");
      contractB.setDep("contractAPost");
      container.getAxiomContracts().add(contractB);
      DbCAxiomContract contractC = DbcmodelFactory.eINSTANCE.createDbCAxiomContract();
      contractC.setName("contractC");
      contractC.setPre("contractBPre");
      contractC.setDep("contractCPost");
      container.getAxiomContracts().add(contractC);
      DbCAxiomContract contractD = DbcmodelFactory.eINSTANCE.createDbCAxiomContract();
      contractD.setName("contractD");
      contractD.setPre("contractDPre");
      contractD.setDep("contractDPost");
      // Execute test
      assertEquals(contractA, container.getAxiomContract(contractA.getPre(), contractA.getDep()));
      assertEquals(contractB, container.getAxiomContract(contractB.getPre(), contractB.getDep()));
      assertEquals(contractC, container.getAxiomContract(contractC.getPre(), contractC.getDep()));
      assertNull(container.getAxiomContract(contractD.getPre(), contractD.getDep()));
   }

} //DbcAxiomTest