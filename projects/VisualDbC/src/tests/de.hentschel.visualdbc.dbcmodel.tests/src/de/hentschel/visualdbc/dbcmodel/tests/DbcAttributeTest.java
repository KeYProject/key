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

import de.hentschel.visualdbc.dbcmodel.DbcAttribute;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;

import junit.framework.TestCase;

import junit.textui.TestRunner;

/**
 * <!-- begin-user-doc -->
 * A test case for the model object '<em><b>Dbc Attribute</b></em>'.
 * <!-- end-user-doc -->
 * @generated
 */
public class DbcAttributeTest extends TestCase {

   /**
    * The fixture for this Dbc Attribute test case.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected DbcAttribute fixture = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static void main(String[] args) {
      TestRunner.run(DbcAttributeTest.class);
   }

   /**
    * Constructs a new Dbc Attribute test case with the given name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcAttributeTest(String name) {
      super(name);
   }

   /**
    * Sets the fixture for this Dbc Attribute test case.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected void setFixture(DbcAttribute fixture) {
      this.fixture = fixture;
   }

   /**
    * Returns the fixture for this Dbc Attribute test case.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected DbcAttribute getFixture() {
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
      setFixture(DbcmodelFactory.eINSTANCE.createDbcAttribute());
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

} //DbcAttributeTest