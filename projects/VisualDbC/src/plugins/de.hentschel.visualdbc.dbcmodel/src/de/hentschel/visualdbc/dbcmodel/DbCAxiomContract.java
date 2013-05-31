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
 * A representation of the model object '<em><b>Db CAxiom Contract</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbCAxiomContract#getPre <em>Pre</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbCAxiomContract#getDep <em>Dep</em>}</li>
 * </ul>
 * </p>
 *
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbCAxiomContract()
 * @model
 * @generated
 */
public interface DbCAxiomContract extends AbstractDbcSpecification, IDbCProvable {
   /**
    * Returns the value of the '<em><b>Pre</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Pre</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Pre</em>' attribute.
    * @see #setPre(String)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbCAxiomContract_Pre()
    * @model
    * @generated
    */
   String getPre();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbCAxiomContract#getPre <em>Pre</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Pre</em>' attribute.
    * @see #getPre()
    * @generated
    */
   void setPre(String value);

   /**
    * Returns the value of the '<em><b>Dep</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Dep</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Dep</em>' attribute.
    * @see #setDep(String)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbCAxiomContract_Dep()
    * @model
    * @generated
    */
   String getDep();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbCAxiomContract#getDep <em>Dep</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Dep</em>' attribute.
    * @see #getDep()
    * @generated
    */
   void setDep(String value);

} // DbCAxiomContract