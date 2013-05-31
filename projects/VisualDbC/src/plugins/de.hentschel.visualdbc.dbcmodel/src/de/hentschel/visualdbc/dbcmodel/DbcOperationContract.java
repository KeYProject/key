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
 * A representation of the model object '<em><b>Dbc Operation Contract</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcOperationContract#getPre <em>Pre</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcOperationContract#getPost <em>Post</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcOperationContract#getModifies <em>Modifies</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcOperationContract#getTermination <em>Termination</em>}</li>
 * </ul>
 * </p>
 *
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcOperationContract()
 * @model
 * @generated
 */
public interface DbcOperationContract extends AbstractDbcSpecification, IDbCProvable {
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
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcOperationContract_Pre()
    * @model
    * @generated
    */
   String getPre();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcOperationContract#getPre <em>Pre</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Pre</em>' attribute.
    * @see #getPre()
    * @generated
    */
   void setPre(String value);

   /**
    * Returns the value of the '<em><b>Post</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Post</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Post</em>' attribute.
    * @see #setPost(String)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcOperationContract_Post()
    * @model
    * @generated
    */
   String getPost();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcOperationContract#getPost <em>Post</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Post</em>' attribute.
    * @see #getPost()
    * @generated
    */
   void setPost(String value);

   /**
    * Returns the value of the '<em><b>Modifies</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Modifies</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Modifies</em>' attribute.
    * @see #setModifies(String)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcOperationContract_Modifies()
    * @model
    * @generated
    */
   String getModifies();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcOperationContract#getModifies <em>Modifies</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Modifies</em>' attribute.
    * @see #getModifies()
    * @generated
    */
   void setModifies(String value);

   /**
    * Returns the value of the '<em><b>Termination</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Termination</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Termination</em>' attribute.
    * @see #setTermination(String)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcOperationContract_Termination()
    * @model
    * @generated
    */
   String getTermination();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcOperationContract#getTermination <em>Termination</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Termination</em>' attribute.
    * @see #getTermination()
    * @generated
    */
   void setTermination(String value);

} // DbcOperationContract