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

import java.util.Properties;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Dbc Model</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcModel#getDriverId <em>Driver Id</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcModel#getConnectionSettings <em>Connection Settings</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcModel#getProofObligations <em>Proof Obligations</em>}</li>
 * </ul>
 * </p>
 *
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcModel()
 * @model
 * @generated
 */
public interface DbcModel extends AbstractDbCContainer {
   /**
    * Returns the value of the '<em><b>Driver Id</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Driver Id</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Driver Id</em>' attribute.
    * @see #setDriverId(String)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcModel_DriverId()
    * @model
    * @generated
    */
   String getDriverId();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcModel#getDriverId <em>Driver Id</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Driver Id</em>' attribute.
    * @see #getDriverId()
    * @generated
    */
   void setDriverId(String value);

   /**
    * Returns the value of the '<em><b>Connection Settings</b></em>' containment reference list.
    * The list contents are of type {@link de.hentschel.visualdbc.dbcmodel.DbcProperty}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Connection Settings</em>' containment reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Connection Settings</em>' containment reference list.
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcModel_ConnectionSettings()
    * @model containment="true"
    * @generated
    */
   EList<DbcProperty> getConnectionSettings();

   /**
    * Returns the value of the '<em><b>Proof Obligations</b></em>' containment reference list.
    * The list contents are of type {@link de.hentschel.visualdbc.dbcmodel.DbcProofObligation}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Proof Obligations</em>' containment reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Proof Obligations</em>' containment reference list.
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcModel_ProofObligations()
    * @model containment="true"
    * @generated
    */
   EList<DbcProofObligation> getProofObligations();

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @model dataType="de.hentschel.visualdbc.dbcmodel.Properties"
    * @generated
    */
   Properties toConnectionProperties();

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @model
    * @generated
    */
   DbcProofObligation getProofObligation(String proofObligation);

} // DbcModel