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
package org.key_project.sed.ui.visualization.model.od.impl;

import java.util.Collection;

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.impl.EObjectImpl;

import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.InternalEList;

import org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer;
import org.key_project.sed.ui.visualization.model.od.ODAssociation;
import org.key_project.sed.ui.visualization.model.od.ODPackage;
import org.key_project.sed.ui.visualization.model.od.ODValue;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Abstract OD Value Container</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.impl.AbstractODValueContainerImpl#getValues <em>Values</em>}</li>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.impl.AbstractODValueContainerImpl#getAssociations <em>Associations</em>}</li>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.impl.AbstractODValueContainerImpl#getName <em>Name</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public abstract class AbstractODValueContainerImpl extends EObjectImpl implements AbstractODValueContainer {
   /**
    * The cached value of the '{@link #getValues() <em>Values</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getValues()
    * @generated
    * @ordered
    */
   protected EList<ODValue> values;

   /**
    * The cached value of the '{@link #getAssociations() <em>Associations</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getAssociations()
    * @generated
    * @ordered
    */
   protected EList<ODAssociation> associations;

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
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected AbstractODValueContainerImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return ODPackage.Literals.ABSTRACT_OD_VALUE_CONTAINER;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<ODValue> getValues() {
      if (values == null) {
         values = new EObjectContainmentEList<ODValue>(ODValue.class, this, ODPackage.ABSTRACT_OD_VALUE_CONTAINER__VALUES);
      }
      return values;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<ODAssociation> getAssociations() {
      if (associations == null) {
         associations = new EObjectContainmentEList<ODAssociation>(ODAssociation.class, this, ODPackage.ABSTRACT_OD_VALUE_CONTAINER__ASSOCIATIONS);
      }
      return associations;
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
         eNotify(new ENotificationImpl(this, Notification.SET, ODPackage.ABSTRACT_OD_VALUE_CONTAINER__NAME, oldName, name));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public NotificationChain eInverseRemove(InternalEObject otherEnd, int featureID, NotificationChain msgs) {
      switch (featureID) {
         case ODPackage.ABSTRACT_OD_VALUE_CONTAINER__VALUES:
            return ((InternalEList<?>)getValues()).basicRemove(otherEnd, msgs);
         case ODPackage.ABSTRACT_OD_VALUE_CONTAINER__ASSOCIATIONS:
            return ((InternalEList<?>)getAssociations()).basicRemove(otherEnd, msgs);
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
         case ODPackage.ABSTRACT_OD_VALUE_CONTAINER__VALUES:
            return getValues();
         case ODPackage.ABSTRACT_OD_VALUE_CONTAINER__ASSOCIATIONS:
            return getAssociations();
         case ODPackage.ABSTRACT_OD_VALUE_CONTAINER__NAME:
            return getName();
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
         case ODPackage.ABSTRACT_OD_VALUE_CONTAINER__VALUES:
            getValues().clear();
            getValues().addAll((Collection<? extends ODValue>)newValue);
            return;
         case ODPackage.ABSTRACT_OD_VALUE_CONTAINER__ASSOCIATIONS:
            getAssociations().clear();
            getAssociations().addAll((Collection<? extends ODAssociation>)newValue);
            return;
         case ODPackage.ABSTRACT_OD_VALUE_CONTAINER__NAME:
            setName((String)newValue);
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
         case ODPackage.ABSTRACT_OD_VALUE_CONTAINER__VALUES:
            getValues().clear();
            return;
         case ODPackage.ABSTRACT_OD_VALUE_CONTAINER__ASSOCIATIONS:
            getAssociations().clear();
            return;
         case ODPackage.ABSTRACT_OD_VALUE_CONTAINER__NAME:
            setName(NAME_EDEFAULT);
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
         case ODPackage.ABSTRACT_OD_VALUE_CONTAINER__VALUES:
            return values != null && !values.isEmpty();
         case ODPackage.ABSTRACT_OD_VALUE_CONTAINER__ASSOCIATIONS:
            return associations != null && !associations.isEmpty();
         case ODPackage.ABSTRACT_OD_VALUE_CONTAINER__NAME:
            return NAME_EDEFAULT == null ? name != null : !NAME_EDEFAULT.equals(name);
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

} //AbstractODValueContainerImpl