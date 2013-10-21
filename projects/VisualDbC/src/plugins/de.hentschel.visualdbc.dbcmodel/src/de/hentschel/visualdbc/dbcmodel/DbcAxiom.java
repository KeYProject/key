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
 * A representation of the model object '<em><b>Dbc Axiom</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcAxiom#getDefinition <em>Definition</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcAxiom#getAxiomContracts <em>Axiom Contracts</em>}</li>
 * </ul>
 * </p>
 *
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcAxiom()
 * @model
 * @generated
 */
public interface DbcAxiom extends IDbCProofReferencable, AbstractDbcSpecification {
    /**
    * Returns the value of the '<em><b>Definition</b></em>' attribute.
    * <!-- begin-user-doc -->
     * <p>
     * If the meaning of the '<em>Definition</em>' attribute isn't clear,
     * there really should be more of a description here...
     * </p>
     * <!-- end-user-doc -->
    * @return the value of the '<em>Definition</em>' attribute.
    * @see #setDefinition(String)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcAxiom_Definition()
    * @model
    * @generated
    */
    String getDefinition();

    /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcAxiom#getDefinition <em>Definition</em>}' attribute.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @param value the new value of the '<em>Definition</em>' attribute.
    * @see #getDefinition()
    * @generated
    */
    void setDefinition(String value);

   /**
    * Returns the value of the '<em><b>Axiom Contracts</b></em>' containment reference list.
    * The list contents are of type {@link de.hentschel.visualdbc.dbcmodel.DbCAxiomContract}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Axiom Contracts</em>' containment reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Axiom Contracts</em>' containment reference list.
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcAxiom_AxiomContracts()
    * @model containment="true"
    * @generated
    */
   EList<DbCAxiomContract> getAxiomContracts();

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @model
    * @generated
    */
   DbCAxiomContract getAxiomContract(String pre, String dep);

} // DbcAxiom