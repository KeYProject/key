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
package org.key_project.sed.ui.visualization.model.od;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Abstract OD Value Container</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer#getValues <em>Values</em>}</li>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer#getAssociations <em>Associations</em>}</li>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer#getName <em>Name</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.key_project.sed.ui.visualization.model.od.ODPackage#getAbstractODValueContainer()
 * @model abstract="true"
 * @generated
 */
public interface AbstractODValueContainer extends EObject {
   /**
    * Returns the value of the '<em><b>Values</b></em>' containment reference list.
    * The list contents are of type {@link org.key_project.sed.ui.visualization.model.od.ODValue}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Values</em>' containment reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Values</em>' containment reference list.
    * @see org.key_project.sed.ui.visualization.model.od.ODPackage#getAbstractODValueContainer_Values()
    * @model containment="true"
    * @generated
    */
   EList<ODValue> getValues();

   /**
    * Returns the value of the '<em><b>Associations</b></em>' containment reference list.
    * The list contents are of type {@link org.key_project.sed.ui.visualization.model.od.ODAssociation}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Associations</em>' containment reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Associations</em>' containment reference list.
    * @see org.key_project.sed.ui.visualization.model.od.ODPackage#getAbstractODValueContainer_Associations()
    * @model containment="true"
    * @generated
    */
   EList<ODAssociation> getAssociations();

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
    * @see org.key_project.sed.ui.visualization.model.od.ODPackage#getAbstractODValueContainer_Name()
    * @model
    * @generated
    */
   String getName();

   /**
    * Sets the value of the '{@link org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer#getName <em>Name</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Name</em>' attribute.
    * @see #getName()
    * @generated
    */
   void setName(String value);

} // AbstractODValueContainer