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
 * A representation of the model object '<em><b>Dbc Invariant</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcInvariant#getCondition <em>Condition</em>}</li>
 * </ul>
 * </p>
 *
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcInvariant()
 * @model
 * @generated
 */
public interface DbcInvariant extends AbstractDbcSpecification, IDbCProofReferencable {
   /**
    * Returns the value of the '<em><b>Condition</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Condition</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Condition</em>' attribute.
    * @see #setCondition(String)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcInvariant_Condition()
    * @model
    * @generated
    */
   String getCondition();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcInvariant#getCondition <em>Condition</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Condition</em>' attribute.
    * @see #getCondition()
    * @generated
    */
   void setCondition(String value);

} // DbcInvariant