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
package de.hentschel.visualdbc.dbcmodel;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.eclipse.emf.common.util.Enumerator;

/**
 * <!-- begin-user-doc -->
 * A representation of the literals of the enumeration '<em><b>Dbc Proof Status</b></em>',
 * and utility methods for working with them.
 * <!-- end-user-doc -->
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcProofStatus()
 * @model
 * @generated
 */
public enum DbcProofStatus implements Enumerator {
   /**
    * The '<em><b>FAILED</b></em>' literal object.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #FAILED_VALUE
    * @generated
    * @ordered
    */
   FAILED(0, "FAILED", "failed"),

   /**
    * The '<em><b>OPEN</b></em>' literal object.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #OPEN_VALUE
    * @generated
    * @ordered
    */
   OPEN(1, "OPEN", "open"),

   /**
    * The '<em><b>FULFILLED</b></em>' literal object.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #FULFILLED_VALUE
    * @generated
    * @ordered
    */
   FULFILLED(2, "FULFILLED", "fulfilled");

   /**
    * The '<em><b>FAILED</b></em>' literal value.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of '<em><b>FAILED</b></em>' literal object isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @see #FAILED
    * @model literal="failed"
    * @generated
    * @ordered
    */
   public static final int FAILED_VALUE = 0;

   /**
    * The '<em><b>OPEN</b></em>' literal value.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of '<em><b>OPEN</b></em>' literal object isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @see #OPEN
    * @model literal="open"
    * @generated
    * @ordered
    */
   public static final int OPEN_VALUE = 1;

   /**
    * The '<em><b>FULFILLED</b></em>' literal value.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of '<em><b>FULFILLED</b></em>' literal object isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @see #FULFILLED
    * @model literal="fulfilled"
    * @generated
    * @ordered
    */
   public static final int FULFILLED_VALUE = 2;

   /**
    * An array of all the '<em><b>Dbc Proof Status</b></em>' enumerators.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private static final DbcProofStatus[] VALUES_ARRAY =
      new DbcProofStatus[] {
         FAILED,
         OPEN,
         FULFILLED,
      };

   /**
    * A public read-only list of all the '<em><b>Dbc Proof Status</b></em>' enumerators.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static final List<DbcProofStatus> VALUES = Collections.unmodifiableList(Arrays.asList(VALUES_ARRAY));

   /**
    * Returns the '<em><b>Dbc Proof Status</b></em>' literal with the specified literal value.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static DbcProofStatus get(String literal) {
      for (int i = 0; i < VALUES_ARRAY.length; ++i) {
         DbcProofStatus result = VALUES_ARRAY[i];
         if (result.toString().equals(literal)) {
            return result;
         }
      }
      return null;
   }

   /**
    * Returns the '<em><b>Dbc Proof Status</b></em>' literal with the specified name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static DbcProofStatus getByName(String name) {
      for (int i = 0; i < VALUES_ARRAY.length; ++i) {
         DbcProofStatus result = VALUES_ARRAY[i];
         if (result.getName().equals(name)) {
            return result;
         }
      }
      return null;
   }

   /**
    * Returns the '<em><b>Dbc Proof Status</b></em>' literal with the specified integer value.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static DbcProofStatus get(int value) {
      switch (value) {
         case FAILED_VALUE: return FAILED;
         case OPEN_VALUE: return OPEN;
         case FULFILLED_VALUE: return FULFILLED;
      }
      return null;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private final int value;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private final String name;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private final String literal;

   /**
    * Only this class can construct instances.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private DbcProofStatus(int value, String name, String literal) {
      this.value = value;
      this.name = name;
      this.literal = literal;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public int getValue() {
     return value;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String getName() {
     return name;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String getLiteral() {
     return literal;
   }

   /**
    * Returns the literal value of the enumerator, which is its string representation.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public String toString() {
      return literal;
   }
   
} //DbcProofStatus