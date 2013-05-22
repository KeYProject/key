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

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Abstract Dbc Operation</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation#getOperationContracts <em>Operation Contracts</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation#getSignature <em>Signature</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation#getVisibility <em>Visibility</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation#isStatic <em>Static</em>}</li>
 * </ul>
 * </p>
 *
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getAbstractDbcOperation()
 * @model abstract="true"
 * @generated
 */
public interface AbstractDbcOperation extends AbstractDbcProofContainer, IDbCProvable {
   /**
    * Returns the value of the '<em><b>Operation Contracts</b></em>' containment reference list.
    * The list contents are of type {@link de.hentschel.visualdbc.dbcmodel.DbcOperationContract}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Operation Contracts</em>' containment reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Operation Contracts</em>' containment reference list.
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getAbstractDbcOperation_OperationContracts()
    * @model containment="true"
    * @generated
    */
   EList<DbcOperationContract> getOperationContracts();

   /**
    * Returns the value of the '<em><b>Signature</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Signature</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Signature</em>' attribute.
    * @see #setSignature(String)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getAbstractDbcOperation_Signature()
    * @model
    * @generated
    */
   String getSignature();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation#getSignature <em>Signature</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Signature</em>' attribute.
    * @see #getSignature()
    * @generated
    */
   void setSignature(String value);

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
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getAbstractDbcOperation_Visibility()
    * @model default="public"
    * @generated
    */
   DbcVisibility getVisibility();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation#getVisibility <em>Visibility</em>}' attribute.
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
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getAbstractDbcOperation_Static()
    * @model
    * @generated
    */
   boolean isStatic();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation#isStatic <em>Static</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Static</em>' attribute.
    * @see #isStatic()
    * @generated
    */
   void setStatic(boolean value);

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @model
    * @generated
    */
   DbcOperationContract getOperationContract(String pre, String post);

} // AbstractDbcOperation