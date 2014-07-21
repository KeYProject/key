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
 * A representation of the literals of the enumeration '<em><b>Dbc Visibility</b></em>',
 * and utility methods for working with them.
 * <!-- end-user-doc -->
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcVisibility()
 * @model
 * @generated
 */
public enum DbcVisibility implements Enumerator {
   /**
    * The '<em><b>DEFAULT</b></em>' literal object.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #DEFAULT_VALUE
    * @generated
    * @ordered
    */
   DEFAULT(0, "DEFAULT", "default"),

   /**
    * The '<em><b>PRIVATE</b></em>' literal object.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #PRIVATE_VALUE
    * @generated
    * @ordered
    */
   PRIVATE(1, "PRIVATE", "private"),

   /**
    * The '<em><b>PROTECTED</b></em>' literal object.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #PROTECTED_VALUE
    * @generated
    * @ordered
    */
   PROTECTED(2, "PROTECTED", "protected"),

   /**
    * The '<em><b>PUBLIC</b></em>' literal object.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #PUBLIC_VALUE
    * @generated
    * @ordered
    */
   PUBLIC(3, "PUBLIC", "public");

   /**
    * The '<em><b>DEFAULT</b></em>' literal value.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of '<em><b>DEFAULT</b></em>' literal object isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @see #DEFAULT
    * @model literal="default"
    * @generated
    * @ordered
    */
   public static final int DEFAULT_VALUE = 0;

   /**
    * The '<em><b>PRIVATE</b></em>' literal value.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of '<em><b>PRIVATE</b></em>' literal object isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @see #PRIVATE
    * @model literal="private"
    * @generated
    * @ordered
    */
   public static final int PRIVATE_VALUE = 1;

   /**
    * The '<em><b>PROTECTED</b></em>' literal value.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of '<em><b>PROTECTED</b></em>' literal object isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @see #PROTECTED
    * @model literal="protected"
    * @generated
    * @ordered
    */
   public static final int PROTECTED_VALUE = 2;

   /**
    * The '<em><b>PUBLIC</b></em>' literal value.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of '<em><b>PUBLIC</b></em>' literal object isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @see #PUBLIC
    * @model literal="public"
    * @generated
    * @ordered
    */
   public static final int PUBLIC_VALUE = 3;

   /**
    * An array of all the '<em><b>Dbc Visibility</b></em>' enumerators.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private static final DbcVisibility[] VALUES_ARRAY =
      new DbcVisibility[] {
         DEFAULT,
         PRIVATE,
         PROTECTED,
         PUBLIC,
      };

   /**
    * A public read-only list of all the '<em><b>Dbc Visibility</b></em>' enumerators.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static final List<DbcVisibility> VALUES = Collections.unmodifiableList(Arrays.asList(VALUES_ARRAY));

   /**
    * Returns the '<em><b>Dbc Visibility</b></em>' literal with the specified literal value.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static DbcVisibility get(String literal) {
      for (int i = 0; i < VALUES_ARRAY.length; ++i) {
         DbcVisibility result = VALUES_ARRAY[i];
         if (result.toString().equals(literal)) {
            return result;
         }
      }
      return null;
   }

   /**
    * Returns the '<em><b>Dbc Visibility</b></em>' literal with the specified name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static DbcVisibility getByName(String name) {
      for (int i = 0; i < VALUES_ARRAY.length; ++i) {
         DbcVisibility result = VALUES_ARRAY[i];
         if (result.getName().equals(name)) {
            return result;
         }
      }
      return null;
   }

   /**
    * Returns the '<em><b>Dbc Visibility</b></em>' literal with the specified integer value.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static DbcVisibility get(int value) {
      switch (value) {
         case DEFAULT_VALUE: return DEFAULT;
         case PRIVATE_VALUE: return PRIVATE;
         case PROTECTED_VALUE: return PROTECTED;
         case PUBLIC_VALUE: return PUBLIC;
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
   private DbcVisibility(int value, String name, String literal) {
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
   
} //DbcVisibility