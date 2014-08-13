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
 * A representation of the model object '<em><b>Dbc Interface</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcInterface#getExtends <em>Extends</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcInterface#getExtendsFullNames <em>Extends Full Names</em>}</li>
 * </ul>
 * </p>
 *
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcInterface()
 * @model
 * @generated
 */
public interface DbcInterface extends AbstractDbcInterface {

   /**
    * Returns the value of the '<em><b>Extends</b></em>' reference list.
    * The list contents are of type {@link de.hentschel.visualdbc.dbcmodel.DbcInterface}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Extends</em>' reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Extends</em>' reference list.
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcInterface_Extends()
    * @model
    * @generated
    */
   EList<DbcInterface> getExtends();

   /**
    * Returns the value of the '<em><b>Extends Full Names</b></em>' attribute list.
    * The list contents are of type {@link java.lang.String}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Extends Full Names</em>' attribute list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Extends Full Names</em>' attribute list.
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcInterface_ExtendsFullNames()
    * @model
    * @generated
    */
   EList<String> getExtendsFullNames();
} // DbcInterface