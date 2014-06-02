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
package org.key_project.sed.ui.visualization.model.od.impl;

import java.util.Collection;

import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.EObjectImpl;

import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.InternalEList;

import org.key_project.sed.ui.visualization.model.od.ODModel;
import org.key_project.sed.ui.visualization.model.od.ODObject;
import org.key_project.sed.ui.visualization.model.od.ODPackage;
import org.key_project.sed.ui.visualization.model.od.ODState;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Model</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.impl.ODModelImpl#getObjects <em>Objects</em>}</li>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.impl.ODModelImpl#getStates <em>States</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ODModelImpl extends EObjectImpl implements ODModel {
   /**
    * The cached value of the '{@link #getObjects() <em>Objects</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getObjects()
    * @generated
    * @ordered
    */
   protected EList<ODObject> objects;

   /**
    * The cached value of the '{@link #getStates() <em>States</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getStates()
    * @generated
    * @ordered
    */
   protected EList<ODState> states;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected ODModelImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return ODPackage.Literals.OD_MODEL;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<ODObject> getObjects() {
      if (objects == null) {
         objects = new EObjectContainmentEList<ODObject>(ODObject.class, this, ODPackage.OD_MODEL__OBJECTS);
      }
      return objects;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<ODState> getStates() {
      if (states == null) {
         states = new EObjectContainmentEList<ODState>(ODState.class, this, ODPackage.OD_MODEL__STATES);
      }
      return states;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public NotificationChain eInverseRemove(InternalEObject otherEnd, int featureID, NotificationChain msgs) {
      switch (featureID) {
         case ODPackage.OD_MODEL__OBJECTS:
            return ((InternalEList<?>)getObjects()).basicRemove(otherEnd, msgs);
         case ODPackage.OD_MODEL__STATES:
            return ((InternalEList<?>)getStates()).basicRemove(otherEnd, msgs);
      }
      return super.eInverseRemove(otherEnd, featureID, msgs);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public Object eGet(int featureID, boolean resolve, boolean coreType) {
      switch (featureID) {
         case ODPackage.OD_MODEL__OBJECTS:
            return getObjects();
         case ODPackage.OD_MODEL__STATES:
            return getStates();
      }
      return super.eGet(featureID, resolve, coreType);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @SuppressWarnings("unchecked")
   @Override
   public void eSet(int featureID, Object newValue) {
      switch (featureID) {
         case ODPackage.OD_MODEL__OBJECTS:
            getObjects().clear();
            getObjects().addAll((Collection<? extends ODObject>)newValue);
            return;
         case ODPackage.OD_MODEL__STATES:
            getStates().clear();
            getStates().addAll((Collection<? extends ODState>)newValue);
            return;
      }
      super.eSet(featureID, newValue);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public void eUnset(int featureID) {
      switch (featureID) {
         case ODPackage.OD_MODEL__OBJECTS:
            getObjects().clear();
            return;
         case ODPackage.OD_MODEL__STATES:
            getStates().clear();
            return;
      }
      super.eUnset(featureID);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public boolean eIsSet(int featureID) {
      switch (featureID) {
         case ODPackage.OD_MODEL__OBJECTS:
            return objects != null && !objects.isEmpty();
         case ODPackage.OD_MODEL__STATES:
            return states != null && !states.isEmpty();
      }
      return super.eIsSet(featureID);
   }

} //ODModelImpl