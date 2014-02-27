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
 * A representation of the model object '<em><b>Dbc Class</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcClass#isAbstract <em>Abstract</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcClass#isFinal <em>Final</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcClass#getExtends <em>Extends</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcClass#isAnonymous <em>Anonymous</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.DbcClass#getExtendsFullNames <em>Extends Full Names</em>}</li>
 * </ul>
 * </p>
 *
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcClass()
 * @model
 * @generated
 */
public interface DbcClass extends AbstractDbcClass {
   /**
    * Returns the value of the '<em><b>Extends</b></em>' reference list.
    * The list contents are of type {@link de.hentschel.visualdbc.dbcmodel.DbcClass}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Extends</em>' reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Extends</em>' reference list.
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcClass_Extends()
    * @model
    * @generated
    */
   EList<DbcClass> getExtends();

   /**
    * Returns the value of the '<em><b>Anonymous</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Anonymous</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Anonymous</em>' attribute.
    * @see #setAnonymous(boolean)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcClass_Anonymous()
    * @model
    * @generated
    */
   boolean isAnonymous();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcClass#isAnonymous <em>Anonymous</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Anonymous</em>' attribute.
    * @see #isAnonymous()
    * @generated
    */
   void setAnonymous(boolean value);

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
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcClass_ExtendsFullNames()
    * @model
    * @generated
    */
   EList<String> getExtendsFullNames();

   /**
    * Returns the value of the '<em><b>Abstract</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Abstract</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Abstract</em>' attribute.
    * @see #setAbstract(boolean)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcClass_Abstract()
    * @model
    * @generated
    */
   boolean isAbstract();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcClass#isAbstract <em>Abstract</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Abstract</em>' attribute.
    * @see #isAbstract()
    * @generated
    */
   void setAbstract(boolean value);

   /**
    * Returns the value of the '<em><b>Final</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Final</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Final</em>' attribute.
    * @see #setFinal(boolean)
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#getDbcClass_Final()
    * @model
    * @generated
    */
   boolean isFinal();

   /**
    * Sets the value of the '{@link de.hentschel.visualdbc.dbcmodel.DbcClass#isFinal <em>Final</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Final</em>' attribute.
    * @see #isFinal()
    * @generated
    */
   void setFinal(boolean value);

} // DbcClass