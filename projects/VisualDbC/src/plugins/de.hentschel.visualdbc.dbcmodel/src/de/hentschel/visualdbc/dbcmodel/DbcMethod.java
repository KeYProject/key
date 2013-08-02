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



/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Dbc Method</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcMethod#getReturnType <em>Return Type</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcMethod#isAbstract <em>Abstract</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcMethod#isFinal <em>Final</em>}</li>
 * </ul>
 * </p>
 *
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcMethod()
 * @model
 * @generated
 */
public interface DbcMethod extends AbstractDbcOperation {
   /**
    * Returns the value of the '<em><b>Return Type</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Return Type</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Return Type</em>' attribute.
    * @see #setReturnType(String)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcMethod_ReturnType()
    * @model
    * @generated
    */
   String getReturnType();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcMethod#getReturnType <em>Return Type</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Return Type</em>' attribute.
    * @see #getReturnType()
    * @generated
    */
   void setReturnType(String value);

   /**
    * Returns the value of the '<em><b>Abstract</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Abstract</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Abstract</em>' attribute.
    * @see #setAbstract(boolean)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcMethod_Abstract()
    * @model
    * @generated
    */
   boolean isAbstract();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcMethod#isAbstract <em>Abstract</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Abstract</em>' attribute.
    * @see #isAbstract()
    * @generated
    */
   void setAbstract(boolean value);

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
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcMethod_Final()
    * @model
    * @generated
    */
   boolean isFinal();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcMethod#isFinal <em>Final</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Final</em>' attribute.
    * @see #isFinal()
    * @generated
    */
   void setFinal(boolean value);

} // DbcMethod