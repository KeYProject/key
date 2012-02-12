/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
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
} // DbcInterface
