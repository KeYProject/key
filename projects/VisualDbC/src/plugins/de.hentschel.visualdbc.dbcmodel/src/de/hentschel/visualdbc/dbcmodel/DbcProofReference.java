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

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Dbc Proof Reference</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcProofReference#getTarget <em>Target</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcProofReference#getKind <em>Kind</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcProofReference#getSource <em>Source</em>}</li>
 * </ul>
 * </p>
 *
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcProofReference()
 * @model
 * @generated
 */
public interface DbcProofReference extends EObject {
   /**
    * Returns the value of the '<em><b>Target</b></em>' reference.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Target</em>' reference isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Target</em>' reference.
    * @see #setTarget(IDbCProofReferencable)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcProofReference_Target()
    * @model
    * @generated
    */
   IDbCProofReferencable getTarget();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcProofReference#getTarget <em>Target</em>}' reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Target</em>' reference.
    * @see #getTarget()
    * @generated
    */
   void setTarget(IDbCProofReferencable value);

   /**
    * Returns the value of the '<em><b>Kind</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Kind</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Kind</em>' attribute.
    * @see #setKind(String)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcProofReference_Kind()
    * @model
    * @generated
    */
   String getKind();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcProofReference#getKind <em>Kind</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Kind</em>' attribute.
    * @see #getKind()
    * @generated
    */
   void setKind(String value);

   /**
    * Returns the value of the '<em><b>Source</b></em>' reference.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Source</em>' reference isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Source</em>' reference.
    * @see #setSource(DbcProof)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcProofReference_Source()
    * @model transient="true"
    * @generated
    */
   DbcProof getSource();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcProofReference#getSource <em>Source</em>}' reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Source</em>' reference.
    * @see #getSource()
    * @generated
    */
   void setSource(DbcProof value);

} // DbcProofReference