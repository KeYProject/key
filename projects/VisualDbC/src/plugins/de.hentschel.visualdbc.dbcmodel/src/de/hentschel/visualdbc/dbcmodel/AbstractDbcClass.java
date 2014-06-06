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
 * A representation of the model object '<em><b>Abstract Dbc Class</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcClass#getConstructors <em>Constructors</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcClass#getImplements <em>Implements</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcClass#getImplementsFullNames <em>Implements Full Names</em>}</li>
 * </ul>
 * </p>
 *
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getAbstractDbcClass()
 * @model abstract="true"
 * @generated
 */
public interface AbstractDbcClass extends AbstractDbcInterface {
   /**
    * Returns the value of the '<em><b>Constructors</b></em>' containment reference list.
    * The list contents are of type {@link de.hentschel.visualdbc.dbcmodel.DbcConstructor}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Constructors</em>' containment reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Constructors</em>' containment reference list.
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getAbstractDbcClass_Constructors()
    * @model containment="true"
    * @generated
    */
   EList<DbcConstructor> getConstructors();

   /**
    * Returns the value of the '<em><b>Implements</b></em>' reference list.
    * The list contents are of type {@link de.hentschel.visualdbc.dbcmodel.DbcInterface}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Implements</em>' reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Implements</em>' reference list.
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getAbstractDbcClass_Implements()
    * @model
    * @generated
    */
   EList<DbcInterface> getImplements();

   /**
    * Returns the value of the '<em><b>Implements Full Names</b></em>' attribute list.
    * The list contents are of type {@link java.lang.String}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Implements Full Names</em>' attribute list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Implements Full Names</em>' attribute list.
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getAbstractDbcClass_ImplementsFullNames()
    * @model default=""
    * @generated
    */
   EList<String> getImplementsFullNames();

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @model
    * @generated
    */
   DbcConstructor getConstructor(String signature);

} // AbstractDbcClass