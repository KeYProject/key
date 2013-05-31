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

import junit.framework.TestCase;
import junit.textui.TestRunner;
import de.hentschel.visualdbc.dbcmodel.DbcConstructor;
import de.hentschel.visualdbc.dbcmodel.DbcMethod;
import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;

/**
 * <!-- begin-user-doc -->
 * A test case for the model object '<em><b>Dbc Proof</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following operations are tested:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcProof#getProofReference(de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable, java.lang.String) <em>Get Proof Reference</em>}</li>
 * </ul>
 * </p>
 * @generated
 */
public class DbcProofTest extends TestCase {

   /**
    * The fixture for this Dbc Proof test case.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected DbcProof fixture = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static void main(String[] args) {
      TestRunner.run(DbcProofTest.class);
   }

   /**
    * Constructs a new Dbc Proof test case with the given name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcProofTest(String name) {
      super(name);
   }

   /**
    * Sets the fixture for this Dbc Proof test case.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected void setFixture(DbcProof fixture) {
      this.fixture = fixture;
   }

   /**
    * Returns the fixture for this Dbc Proof test case.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected DbcProof getFixture() {
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
      setFixture(DbcmodelFactory.eINSTANCE.createDbcProof());
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
    * Tests the '{@link de.hentschel.visualdbc.dbcmodel.DbcProof#getProofReference(de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable, java.lang.String) <em>Get Proof Reference</em>}' operation.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.DbcProof#getProofReference(de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable, java.lang.String)
    * @generated NOT
    */
   public void testGetProofReference__IDbCProofReferencable_String() {
      // Create model
      DbcMethod targetA = DbcmodelFactory.eINSTANCE.createDbcMethod();
      DbcConstructor targetB = DbcmodelFactory.eINSTANCE.createDbcConstructor();
      DbcProof container = DbcmodelFactory.eINSTANCE.createDbcProof();
      DbcProofReference referenceA = DbcmodelFactory.eINSTANCE.createDbcProofReference();
      referenceA.setKind("referenceA");
      referenceA.setTarget(targetA);
      container.getProofReferences().add(referenceA);
      DbcProofReference referenceB = DbcmodelFactory.eINSTANCE.createDbcProofReference();
      referenceB.setKind("referenceB");
      referenceB.setTarget(targetA);
      container.getProofReferences().add(referenceB);
      DbcProofReference referenceC = DbcmodelFactory.eINSTANCE.createDbcProofReference();
      referenceC.setKind("referenceC");
      referenceC.setTarget(targetA);
      container.getProofReferences().add(referenceC);
      DbcProofReference referenceD = DbcmodelFactory.eINSTANCE.createDbcProofReference();
      referenceD.setKind("referenceD");
      referenceD.setTarget(targetA);
      DbcProofReference referenceE = DbcmodelFactory.eINSTANCE.createDbcProofReference();
      referenceE.setKind("referenceE");
      referenceE.setTarget(targetB);
      container.getProofReferences().add(referenceE);
      // Execute test
      assertEquals(referenceA, container.getProofReference(referenceA.getTarget(), referenceA.getKind()));
      assertEquals(referenceB, container.getProofReference(referenceB.getTarget(), referenceB.getKind()));
      assertEquals(referenceC, container.getProofReference(referenceC.getTarget(), referenceC.getKind()));
      assertNull(container.getProofReference(referenceD.getTarget(), referenceD.getKind()));
      assertEquals(referenceE, container.getProofReference(referenceE.getTarget(), referenceE.getKind()));
      assertNull(container.getProofReference(targetA, referenceD.getKind()));
      assertNull(container.getProofReference(referenceE.getTarget(), "INVALID"));
   }
} //DbcProofTest