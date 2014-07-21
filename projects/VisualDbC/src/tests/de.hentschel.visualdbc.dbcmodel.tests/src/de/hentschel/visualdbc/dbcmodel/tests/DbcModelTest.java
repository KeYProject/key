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

import java.util.Properties;

import junit.textui.TestRunner;

import org.eclipse.emf.common.util.EList;

import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.DbcProofObligation;
import de.hentschel.visualdbc.dbcmodel.DbcProperty;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;

/**
 * <!-- begin-user-doc -->
 * A test case for the model object '<em><b>Dbc Model</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following operations are tested:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcModel#toConnectionProperties() <em>To Connection Properties</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcModel#getProofObligation(java.lang.String) <em>Get Proof Obligation</em>}</li>
 * </ul>
 * </p>
 * @generated
 */
public class DbcModelTest extends AbstractDbCContainerTest {

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static void main(String[] args) {
      TestRunner.run(DbcModelTest.class);
   }

   /**
    * Constructs a new Dbc Model test case with the given name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcModelTest(String name) {
      super(name);
   }

   /**
    * Returns the fixture for this Dbc Model test case.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected DbcModel getFixture() {
      return (DbcModel)fixture;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see junit.framework.TestCase#setUp()
    * @generated
    */
   @Override
   protected void setUp() throws Exception {
      setFixture(DbcmodelFactory.eINSTANCE.createDbcModel());
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
    * Tests the '{@link de.hentschel.visualdbc.dbcmodel.DbcModel#toConnectionProperties() <em>To Connection Properties</em>}' operation.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.DbcModel#toConnectionProperties()
    * @generated NOT
    */
   public void testToConnectionProperties() {
      DbcModel model = DbcmodelFactory.eINSTANCE.createDbcModel();
      // Test no properties
      Properties result = model.toConnectionProperties();
      compare(model.getConnectionSettings(), result);
      // Add one property
      DbcProperty propA = DbcmodelFactory.eINSTANCE.createDbcProperty();
      propA.setKey("A");
      propA.setValue("A-Value");
      compare(model.getConnectionSettings(), result);
      // Add second property
      DbcProperty propB = DbcmodelFactory.eINSTANCE.createDbcProperty();
      propB.setKey("B");
      propB.setValue("B-Value");
      compare(model.getConnectionSettings(), result);
      // Add empty value
      DbcProperty propC = DbcmodelFactory.eINSTANCE.createDbcProperty();
      propC.setKey("C");
      propC.setValue("");
      compare(model.getConnectionSettings(), result);
      // Add null value
      DbcProperty propD = DbcmodelFactory.eINSTANCE.createDbcProperty();
      propD.setKey("D");
      propD.setValue(null);
      compare(model.getConnectionSettings(), result);
      // Add empty key
      DbcProperty propEmptyKey = DbcmodelFactory.eINSTANCE.createDbcProperty();
      propEmptyKey.setKey("");
      propEmptyKey.setValue("empty-value");
      compare(model.getConnectionSettings(), result);
      // Add null key
      DbcProperty propNullKey = DbcmodelFactory.eINSTANCE.createDbcProperty();
      propNullKey.setKey(null);
      propNullKey.setValue("null-value");
      compare(model.getConnectionSettings(), result);
   }

   /**
    * Tests the '{@link de.hentschel.visualdbc.dbcmodel.DbcModel#getProofObligation(java.lang.String) <em>Get Proof Obligation</em>}' operation.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.DbcModel#getProofObligation(java.lang.String)
    * @generated NOT
    */
   public void testGetProofObligation__String() {
      // Create model
      DbcModel model = DbcmodelFactory.eINSTANCE.createDbcModel();
      DbcProofObligation obligationA = DbcmodelFactory.eINSTANCE.createDbcProofObligation();
      obligationA.setObligation("obligationA");
      model.getProofObligations().add(obligationA);
      DbcProofObligation obligationB = DbcmodelFactory.eINSTANCE.createDbcProofObligation();
      obligationB.setObligation("obligationB");
      model.getProofObligations().add(obligationB);
      DbcProofObligation obligationC = DbcmodelFactory.eINSTANCE.createDbcProofObligation();
      obligationC.setObligation("obligationC");
      model.getProofObligations().add(obligationC);
      DbcProofObligation obligationD = DbcmodelFactory.eINSTANCE.createDbcProofObligation();
      obligationD.setObligation("obligationD");
      // Execute test
      assertEquals(obligationA, model.getProofObligation(obligationA.getObligation()));
      assertEquals(obligationB, model.getProofObligation(obligationB.getObligation()));
      assertEquals(obligationC, model.getProofObligation(obligationC.getObligation()));
      assertNull(model.getProofObligation(obligationD.getObligation()));
   }

   /**
    * Compares the given key value pairs.
    * @param connectionSettings The expected value pairs.
    * @param result The current value pairs.
    * @generated NOT
    */
   protected void compare(EList<DbcProperty> connectionSettings, Properties result) {
      assertEquals(connectionSettings.size(), result.size());
      for (DbcProperty property : connectionSettings) {
         assertTrue(result.containsKey(property.getKey()));
         assertEquals(property.getValue(), result.getProperty(property.getKey()));
      }
   }
} //DbcModelTest