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

import de.hentschel.visualdbc.dbcmodel.DbcInterface;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;

import junit.textui.TestRunner;

/**
 * <!-- begin-user-doc -->
 * A test case for the model object '<em><b>Dbc Interface</b></em>'.
 * <!-- end-user-doc -->
 * @generated
 */
public class DbcInterfaceTest extends AbstractDbcInterfaceTest {

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static void main(String[] args) {
      TestRunner.run(DbcInterfaceTest.class);
   }

   /**
    * Constructs a new Dbc Interface test case with the given name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcInterfaceTest(String name) {
      super(name);
   }

   /**
    * Returns the fixture for this Dbc Interface test case.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected DbcInterface getFixture() {
      return (DbcInterface)fixture;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see junit.framework.TestCase#setUp()
    * @generated
    */
   @Override
   protected void setUp() throws Exception {
      setFixture(DbcmodelFactory.eINSTANCE.createDbcInterface());
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

} //DbcInterfaceTest