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
 * A representation of the model object '<em><b>Dbc Property</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcProperty#getKey <em>Key</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcProperty#getValue <em>Value</em>}</li>
 * </ul>
 * </p>
 *
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcProperty()
 * @model
 * @generated
 */
public interface DbcProperty extends EObject {
   /**
    * Returns the value of the '<em><b>Key</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Key</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Key</em>' attribute.
    * @see #setKey(String)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcProperty_Key()
    * @model
    * @generated
    */
   String getKey();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcProperty#getKey <em>Key</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Key</em>' attribute.
    * @see #getKey()
    * @generated
    */
   void setKey(String value);

   /**
    * Returns the value of the '<em><b>Value</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Value</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Value</em>' attribute.
    * @see #setValue(String)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcProperty_Value()
    * @model
    * @generated
    */
   String getValue();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcProperty#getValue <em>Value</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Value</em>' attribute.
    * @see #getValue()
    * @generated
    */
   void setValue(String value);

} // DbcProperty