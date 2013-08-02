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
package de.hentschel.visualdbc.dbcmodel;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Dbc Proof</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcProof#getTarget <em>Target</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcProof#getProofReferences <em>Proof References</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcProof#getObligation <em>Obligation</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcProof#getStatus <em>Status</em>}</li>
 * </ul>
 * </p>
 *
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcProof()
 * @model
 * @generated
 */
public interface DbcProof extends EObject {
   /**
    * Returns the value of the '<em><b>Obligation</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Obligation</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Obligation</em>' attribute.
    * @see #setObligation(String)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcProof_Obligation()
    * @model
    * @generated
    */
   String getObligation();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcProof#getObligation <em>Obligation</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Obligation</em>' attribute.
    * @see #getObligation()
    * @generated
    */
   void setObligation(String value);

   /**
    * Returns the value of the '<em><b>Target</b></em>' reference.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Target</em>' reference isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Target</em>' reference.
    * @see #setTarget(IDbCProvable)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcProof_Target()
    * @model
    * @generated
    */
   IDbCProvable getTarget();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcProof#getTarget <em>Target</em>}' reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Target</em>' reference.
    * @see #getTarget()
    * @generated
    */
   void setTarget(IDbCProvable value);

   /**
    * Returns the value of the '<em><b>Proof References</b></em>' containment reference list.
    * The list contents are of type {@link de.hentschel.visualdbc.dbcmodel.DbcProofReference}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Proof References</em>' containment reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Proof References</em>' containment reference list.
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcProof_ProofReferences()
    * @model containment="true"
    * @generated
    */
   EList<DbcProofReference> getProofReferences();

   /**
    * Returns the value of the '<em><b>Status</b></em>' attribute.
    * The default value is <code>"open"</code>.
    * The literals are from the enumeration {@link de.hentschel.visualdbc.dbcmodel.DbcProofStatus}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Status</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Status</em>' attribute.
    * @see de.hentschel.visualdbc.dbcmodel.DbcProofStatus
    * @see #setStatus(DbcProofStatus)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcProof_Status()
    * @model default="open"
    * @generated
    */
   DbcProofStatus getStatus();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcProof#getStatus <em>Status</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Status</em>' attribute.
    * @see de.hentschel.visualdbc.dbcmodel.DbcProofStatus
    * @see #getStatus()
    * @generated
    */
   void setStatus(DbcProofStatus value);

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @model
    * @generated
    */
   DbcProofReference getProofReference(IDbCProofReferencable target, String kind);

} // DbcProof