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
 * A representation of the model object '<em><b>Model</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.ODModel#getObjects <em>Objects</em>}</li>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.ODModel#getStates <em>States</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.key_project.sed.ui.visualization.model.od.ODPackage#getODModel()
 * @model
 * @generated
 */
public interface ODModel extends EObject {
   /**
    * Returns the value of the '<em><b>Objects</b></em>' containment reference list.
    * The list contents are of type {@link org.key_project.sed.ui.visualization.model.od.ODObject}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Objects</em>' containment reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Objects</em>' containment reference list.
    * @see org.key_project.sed.ui.visualization.model.od.ODPackage#getODModel_Objects()
    * @model containment="true"
    * @generated
    */
   EList<ODObject> getObjects();

   /**
    * Returns the value of the '<em><b>States</b></em>' containment reference list.
    * The list contents are of type {@link org.key_project.sed.ui.visualization.model.od.ODState}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>States</em>' containment reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>States</em>' containment reference list.
    * @see org.key_project.sed.ui.visualization.model.od.ODPackage#getODModel_States()
    * @model containment="true"
    * @generated
    */
   EList<ODState> getStates();

} // ODModel