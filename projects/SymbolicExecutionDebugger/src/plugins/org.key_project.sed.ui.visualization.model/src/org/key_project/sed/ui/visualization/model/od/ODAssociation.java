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
package org.key_project.sed.ui.visualization.model.od;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Association</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.ODAssociation#getName <em>Name</em>}</li>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.ODAssociation#getTarget <em>Target</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.key_project.sed.ui.visualization.model.od.ODPackage#getODAssociation()
 * @model
 * @generated
 */
public interface ODAssociation extends EObject {
   /**
    * Returns the value of the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Name</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Name</em>' attribute.
    * @see #setName(String)
    * @see org.key_project.sed.ui.visualization.model.od.ODPackage#getODAssociation_Name()
    * @model
    * @generated
    */
   String getName();

   /**
    * Sets the value of the '{@link org.key_project.sed.ui.visualization.model.od.ODAssociation#getName <em>Name</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Name</em>' attribute.
    * @see #getName()
    * @generated
    */
   void setName(String value);

   /**
    * Returns the value of the '<em><b>Target</b></em>' reference.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Target</em>' reference isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Target</em>' reference.
    * @see #setTarget(ODObject)
    * @see org.key_project.sed.ui.visualization.model.od.ODPackage#getODAssociation_Target()
    * @model required="true"
    * @generated
    */
   ODObject getTarget();

   /**
    * Sets the value of the '{@link org.key_project.sed.ui.visualization.model.od.ODAssociation#getTarget <em>Target</em>}' reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Target</em>' reference.
    * @see #getTarget()
    * @generated
    */
   void setTarget(ODObject value);

} // ODAssociation