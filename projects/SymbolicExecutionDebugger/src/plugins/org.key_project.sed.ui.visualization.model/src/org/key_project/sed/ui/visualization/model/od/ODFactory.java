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

import org.eclipse.emf.ecore.EFactory;

/**
 * <!-- begin-user-doc -->
 * The <b>Factory</b> for the model.
 * It provides a create method for each non-abstract class of the model.
 * <!-- end-user-doc -->
 * @see org.key_project.sed.ui.visualization.model.od.ODPackage
 * @generated
 */
public interface ODFactory extends EFactory {
   /**
    * The singleton instance of the factory.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   ODFactory eINSTANCE = org.key_project.sed.ui.visualization.model.od.impl.ODFactoryImpl.init();

   /**
    * Returns a new object of class '<em>Object</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Object</em>'.
    * @generated
    */
   ODObject createODObject();

   /**
    * Returns a new object of class '<em>Value</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Value</em>'.
    * @generated
    */
   ODValue createODValue();

   /**
    * Returns a new object of class '<em>Model</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Model</em>'.
    * @generated
    */
   ODModel createODModel();

   /**
    * Returns a new object of class '<em>Association</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Association</em>'.
    * @generated
    */
   ODAssociation createODAssociation();

   /**
    * Returns a new object of class '<em>State</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>State</em>'.
    * @generated
    */
   ODState createODState();

   /**
    * Returns the package supported by this factory.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the package supported by this factory.
    * @generated
    */
   ODPackage getODPackage();

} //ODFactory