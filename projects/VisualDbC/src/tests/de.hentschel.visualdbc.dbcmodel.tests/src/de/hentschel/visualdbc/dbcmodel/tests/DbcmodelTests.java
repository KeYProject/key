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

import junit.framework.Test;
import junit.framework.TestSuite;

import junit.textui.TestRunner;

/**
 * <!-- begin-user-doc -->
 * A test suite for the '<em><b>dbcmodel</b></em>' package.
 * <!-- end-user-doc -->
 * @generated
 */
public class DbcmodelTests extends TestSuite {

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
      TestSuite suite = new DbcmodelTests("dbcmodel Tests");
      suite.addTestSuite(DbcModelTest.class);
      suite.addTestSuite(DbcPackageTest.class);
      suite.addTestSuite(DbcClassTest.class);
      suite.addTestSuite(DbcMethodTest.class);
      suite.addTestSuite(DbcProofTest.class);
      suite.addTestSuite(DbcConstructorTest.class);
      suite.addTestSuite(DbcInterfaceTest.class);
      suite.addTestSuite(DbcEnumTest.class);
      suite.addTestSuite(DbcAxiomTest.class);
      return suite;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcmodelTests(String name) {
      super(name);
   }

} //DbcmodelTests