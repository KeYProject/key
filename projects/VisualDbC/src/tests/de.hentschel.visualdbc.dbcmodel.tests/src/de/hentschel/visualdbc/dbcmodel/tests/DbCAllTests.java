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

import junit.framework.Test;
import junit.framework.TestSuite;

import junit.textui.TestRunner;

/**
 * <!-- begin-user-doc -->
 * A test suite for the '<em><b>DbC</b></em>' model.
 * <!-- end-user-doc -->
 * @generated
 */
public class DbCAllTests extends TestSuite {

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static void main(String[] args) {
      TestRunner.run(suite());
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static Test suite() {
      TestSuite suite = new DbCAllTests("DbC Tests");
      suite.addTest(DbcmodelTests.suite());
      return suite;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbCAllTests(String name) {
      super(name);
   }

} //DbCAllTests
