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
 * A representation of the model object '<em><b>Dbc Proof Obligation</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcProofObligation#getObligation <em>Obligation</em>}</li>
 * </ul>
 * </p>
 *
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcProofObligation()
 * @model
 * @generated
 */
public interface DbcProofObligation extends EObject {
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
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcProofObligation_Obligation()
    * @model
    * @generated
    */
   String getObligation();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcProofObligation#getObligation <em>Obligation</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Obligation</em>' attribute.
    * @see #getObligation()
    * @generated
    */
   void setObligation(String value);

} // DbcProofObligation