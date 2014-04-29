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
package de.hentschel.visualdbc.dbcmodel.impl;

import de.hentschel.visualdbc.dbcmodel.DbcProperty;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;

import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.ecore.EClass;

import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.impl.EObjectImpl;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Dbc Property</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcPropertyImpl#getKey <em>Key</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcPropertyImpl#getValue <em>Value</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class DbcPropertyImpl extends EObjectImpl implements DbcProperty {
   /**
    * The default value of the '{@link #getKey() <em>Key</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getKey()
    * @generated
    * @ordered
    */
   protected static final String KEY_EDEFAULT = null;

   /**
    * The cached value of the '{@link #getKey() <em>Key</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getKey()
    * @generated
    * @ordered
    */
   protected String key = KEY_EDEFAULT;

   /**
    * The default value of the '{@link #getValue() <em>Value</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getValue()
    * @generated
    * @ordered
    */
   protected static final String VALUE_EDEFAULT = null;

   /**
    * The cached value of the '{@link #getValue() <em>Value</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getValue()
    * @generated
    * @ordered
    */
   protected String value = VALUE_EDEFAULT;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected DbcPropertyImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return DbcmodelPackage.Literals.DBC_PROPERTY;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String getKey() {
      return key;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setKey(String newKey) {
      String oldKey = key;
      key = newKey;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DBC_PROPERTY__KEY, oldKey, key));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String getValue() {
      return value;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setValue(String newValue) {
      String oldValue = value;
      value = newValue;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DBC_PROPERTY__VALUE, oldValue, value));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public Object eGet(int featureID, boolean resolve, boolean coreType) {
      switch (featureID) {
         case DbcmodelPackage.DBC_PROPERTY__KEY:
            return getKey();
         case DbcmodelPackage.DBC_PROPERTY__VALUE:
            return getValue();
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
         case DbcmodelPackage.DBC_PROPERTY__KEY:
            setKey((String)newValue);
            return;
         case DbcmodelPackage.DBC_PROPERTY__VALUE:
            setValue((String)newValue);
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
         case DbcmodelPackage.DBC_PROPERTY__KEY:
            setKey(KEY_EDEFAULT);
            return;
         case DbcmodelPackage.DBC_PROPERTY__VALUE:
            setValue(VALUE_EDEFAULT);
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
         case DbcmodelPackage.DBC_PROPERTY__KEY:
            return KEY_EDEFAULT == null ? key != null : !KEY_EDEFAULT.equals(key);
         case DbcmodelPackage.DBC_PROPERTY__VALUE:
            return VALUE_EDEFAULT == null ? value != null : !VALUE_EDEFAULT.equals(value);
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
      result.append(" (key: ");
      result.append(key);
      result.append(", value: ");
      result.append(value);
      result.append(')');
      return result.toString();
   }

} //DbcPropertyImpl