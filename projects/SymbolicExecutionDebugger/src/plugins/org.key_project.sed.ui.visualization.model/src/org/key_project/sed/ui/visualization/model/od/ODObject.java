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


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Object</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.ODObject#getType <em>Type</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.key_project.sed.ui.visualization.model.od.ODPackage#getODObject()
 * @model
 * @generated
 */
public interface ODObject extends AbstractODValueContainer {
   /**
    * Returns the value of the '<em><b>Type</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Type</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Type</em>' attribute.
    * @see #setType(String)
    * @see org.key_project.sed.ui.visualization.model.od.ODPackage#getODObject_Type()
    * @model
    * @generated
    */
   String getType();

   /**
    * Sets the value of the '{@link org.key_project.sed.ui.visualization.model.od.ODObject#getType <em>Type</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Type</em>' attribute.
    * @see #getType()
    * @generated
    */
   void setType(String value);

} // ODObject