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


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Dbc Attribute</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcAttribute#getName <em>Name</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcAttribute#getType <em>Type</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcAttribute#getVisibility <em>Visibility</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcAttribute#isStatic <em>Static</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcAttribute#isFinal <em>Final</em>}</li>
 * </ul>
 * </p>
 *
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcAttribute()
 * @model
 * @generated
 */
public interface DbcAttribute extends IDbCProofReferencable {
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
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcAttribute_Name()
    * @model
    * @generated
    */
   String getName();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcAttribute#getName <em>Name</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Name</em>' attribute.
    * @see #getName()
    * @generated
    */
   void setName(String value);

   /**
    * Returns the value of the '<em><b>Type</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Type</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Type</em>' attribute.
    * @see #setType(String)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcAttribute_Type()
    * @model
    * @generated
    */
   String getType();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcAttribute#getType <em>Type</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Type</em>' attribute.
    * @see #getType()
    * @generated
    */
   void setType(String value);

   /**
    * Returns the value of the '<em><b>Visibility</b></em>' attribute.
    * The default value is <code>"private"</code>.
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
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcAttribute_Visibility()
    * @model default="private"
    * @generated
    */
   DbcVisibility getVisibility();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcAttribute#getVisibility <em>Visibility</em>}' attribute.
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
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcAttribute_Static()
    * @model
    * @generated
    */
   boolean isStatic();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcAttribute#isStatic <em>Static</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Static</em>' attribute.
    * @see #isStatic()
    * @generated
    */
   void setStatic(boolean value);

   /**
    * Returns the value of the '<em><b>Final</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Final</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Final</em>' attribute.
    * @see #setFinal(boolean)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcAttribute_Final()
    * @model
    * @generated
    */
   boolean isFinal();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcAttribute#isFinal <em>Final</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Final</em>' attribute.
    * @see #isFinal()
    * @generated
    */
   void setFinal(boolean value);

} // DbcAttribute