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
 * A representation of the model object '<em><b>IDb CProvable</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.IDbCProvable#getProofObligations <em>Proof Obligations</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.IDbCProvable#getAllProofs <em>All Proofs</em>}</li>
 * </ul>
 * </p>
 *
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getIDbCProvable()
 * @model interface="true" abstract="true"
 * @generated
 */
public interface IDbCProvable extends IDbCProofReferencable {

   /**
    * Returns the value of the '<em><b>Proof Obligations</b></em>' reference list.
    * The list contents are of type {@link de.hentschel.visualdbc.dbcmodel.DbcProofObligation}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Proof Obligations</em>' reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Proof Obligations</em>' reference list.
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getIDbCProvable_ProofObligations()
    * @model
    * @generated
    */
   EList<DbcProofObligation> getProofObligations();

   /**
    * Returns the value of the '<em><b>All Proofs</b></em>' reference list.
    * The list contents are of type {@link de.hentschel.visualdbc.dbcmodel.DbcProof}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>All Proofs</em>' reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>All Proofs</em>' reference list.
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getIDbCProvable_AllProofs()
    * @model transient="true" changeable="false"
    * @generated
    */
   EList<DbcProof> getAllProofs();
} // IDbCProvable