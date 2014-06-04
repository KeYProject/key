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

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Abstract Dbc Type</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcType#getName <em>Name</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcType#getVisibility <em>Visibility</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcType#isStatic <em>Static</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcType#getInvariants <em>Invariants</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcType#getAxioms <em>Axioms</em>}</li>
 * </ul>
 * </p>
 *
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getAbstractDbcType()
 * @model abstract="true"
 * @generated
 */
public interface AbstractDbcType extends AbstractDbcTypeContainer, IDbCProvable {
   /**
    * Returns the value of the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Name</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Name</em>' attribute.
    * @see #setName(String)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getAbstractDbcType_Name()
    * @model
    * @generated
    */
   String getName();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcType#getName <em>Name</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Name</em>' attribute.
    * @see #getName()
    * @generated
    */
   void setName(String value);

   /**
    * Returns the value of the '<em><b>Visibility</b></em>' attribute.
    * The default value is <code>"public"</code>.
    * The literals are from the enumeration {@link de.hentschel.visualdbc.dbcmodel.DbcVisibility}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Visibility</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Visibility</em>' attribute.
    * @see de.hentschel.visualdbc.dbcmodel.DbcVisibility
    * @see #setVisibility(DbcVisibility)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getAbstractDbcType_Visibility()
    * @model default="public"
    * @generated
    */
   DbcVisibility getVisibility();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcType#getVisibility <em>Visibility</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Visibility</em>' attribute.
    * @see de.hentschel.visualdbc.dbcmodel.DbcVisibility
    * @see #getVisibility()
    * @generated
    */
   void setVisibility(DbcVisibility value);

   /**
    * Returns the value of the '<em><b>Static</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Static</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Static</em>' attribute.
    * @see #setStatic(boolean)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getAbstractDbcType_Static()
    * @model
    * @generated
    */
   boolean isStatic();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcType#isStatic <em>Static</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Static</em>' attribute.
    * @see #isStatic()
    * @generated
    */
   void setStatic(boolean value);

   /**
    * Returns the value of the '<em><b>Invariants</b></em>' containment reference list.
    * The list contents are of type {@link de.hentschel.visualdbc.dbcmodel.DbcInvariant}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Invariants</em>' containment reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Invariants</em>' containment reference list.
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getAbstractDbcType_Invariants()
    * @model containment="true"
    * @generated
    */
   EList<DbcInvariant> getInvariants();

   /**
    * Returns the value of the '<em><b>Axioms</b></em>' containment reference list.
    * The list contents are of type {@link de.hentschel.visualdbc.dbcmodel.DbcAxiom}.
    * <!-- begin-user-doc -->
     * <p>
     * If the meaning of the '<em>Axioms</em>' containment reference list isn't clear,
     * there really should be more of a description here...
     * </p>
     * <!-- end-user-doc -->
    * @return the value of the '<em>Axioms</em>' containment reference list.
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getAbstractDbcType_Axioms()
    * @model containment="true"
    * @generated
    */
    EList<DbcAxiom> getAxioms();

/**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @model
    * @generated
    */
   DbcInvariant getInvariant(String condition);

/**
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @model
    * @generated
    */
    DbcAxiom getAxiom(String definition);

} // AbstractDbcType