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

import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.impl.EObjectImpl;

import org.key_project.sed.ui.visualization.model.od.ODAssociation;
import org.key_project.sed.ui.visualization.model.od.ODObject;
import org.key_project.sed.ui.visualization.model.od.ODPackage;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Association</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.impl.ODAssociationImpl#getName <em>Name</em>}</li>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.impl.ODAssociationImpl#getTarget <em>Target</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ODAssociationImpl extends EObjectImpl implements ODAssociation {
   /**
    * The default value of the '{@link #getName() <em>Name</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getName()
    * @generated
    * @ordered
    */
   protected static final String NAME_EDEFAULT = null;

   /**
    * The cached value of the '{@link #getName() <em>Name</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getName()
    * @generated
    * @ordered
    */
   protected String name = NAME_EDEFAULT;

   /**
    * The cached value of the '{@link #getTarget() <em>Target</em>}' reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getTarget()
    * @generated
    * @ordered
    */
   protected ODObject target;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected ODAssociationImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return ODPackage.Literals.OD_ASSOCIATION;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String getName() {
      return name;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setName(String newName) {
      String oldName = name;
      name = newName;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, ODPackage.OD_ASSOCIATION__NAME, oldName, name));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public ODObject getTarget() {
      if (target != null && target.eIsProxy()) {
         InternalEObject oldTarget = (InternalEObject)target;
         target = (ODObject)eResolveProxy(oldTarget);
         if (target != oldTarget) {
            if (eNotificationRequired())
               eNotify(new ENotificationImpl(this, Notification.RESOLVE, ODPackage.OD_ASSOCIATION__TARGET, oldTarget, target));
         }
      }
      return target;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public ODObject basicGetTarget() {
      return target;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setTarget(ODObject newTarget) {
      ODObject oldTarget = target;
      target = newTarget;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, ODPackage.OD_ASSOCIATION__TARGET, oldTarget, target));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public Object eGet(int featureID, boolean resolve, boolean coreType) {
      switch (featureID) {
         case ODPackage.OD_ASSOCIATION__NAME:
            return getName();
         case ODPackage.OD_ASSOCIATION__TARGET:
            if (resolve) return getTarget();
            return basicGetTarget();
      }
      return super.eGet(featureID, resolve, coreType);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public void eSet(int featureID, Object newValue) {
      switch (featureID) {
         case ODPackage.OD_ASSOCIATION__NAME:
            setName((String)newValue);
            return;
         case ODPackage.OD_ASSOCIATION__TARGET:
            setTarget((ODObject)newValue);
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
         case ODPackage.OD_ASSOCIATION__NAME:
            setName(NAME_EDEFAULT);
            return;
         case ODPackage.OD_ASSOCIATION__TARGET:
            setTarget((ODObject)null);
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
         case ODPackage.OD_ASSOCIATION__NAME:
            return NAME_EDEFAULT == null ? name != null : !NAME_EDEFAULT.equals(name);
         case ODPackage.OD_ASSOCIATION__TARGET:
            return target != null;
      }
      return super.eIsSet(featureID);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public String toString() {
      if (eIsProxy()) return super.toString();

      StringBuffer result = new StringBuffer(super.toString());
      result.append(" (name: ");
      result.append(name);
      result.append(')');
      return result.toString();
   }

} //ODAssociationImpl