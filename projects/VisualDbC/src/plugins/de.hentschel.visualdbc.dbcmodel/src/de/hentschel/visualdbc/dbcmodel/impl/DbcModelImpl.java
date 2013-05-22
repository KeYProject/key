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
package de.hentschel.visualdbc.dbcmodel.impl;

import java.util.Collection;
import java.util.Iterator;
import java.util.Properties;

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.NotificationChain;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;
import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.InternalEList;

import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.DbcProofObligation;
import de.hentschel.visualdbc.dbcmodel.DbcProperty;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Dbc Model</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcModelImpl#getDriverId <em>Driver Id</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcModelImpl#getConnectionSettings <em>Connection Settings</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcModelImpl#getProofObligations <em>Proof Obligations</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class DbcModelImpl extends AbstractDbCContainerImpl implements DbcModel {
   /**
    * The default value of the '{@link #getDriverId() <em>Driver Id</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getDriverId()
    * @generated
    * @ordered
    */
   protected static final String DRIVER_ID_EDEFAULT = null;

   /**
    * The cached value of the '{@link #getDriverId() <em>Driver Id</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getDriverId()
    * @generated
    * @ordered
    */
   protected String driverId = DRIVER_ID_EDEFAULT;

   /**
    * The cached value of the '{@link #getConnectionSettings() <em>Connection Settings</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getConnectionSettings()
    * @generated
    * @ordered
    */
   protected EList<DbcProperty> connectionSettings;

   /**
    * The cached value of the '{@link #getProofObligations() <em>Proof Obligations</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getProofObligations()
    * @generated
    * @ordered
    */
   protected EList<DbcProofObligation> proofObligations;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected DbcModelImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return DbcmodelPackage.Literals.DBC_MODEL;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String getDriverId() {
      return driverId;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setDriverId(String newDriverId) {
      String oldDriverId = driverId;
      driverId = newDriverId;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DBC_MODEL__DRIVER_ID, oldDriverId, driverId));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<DbcProperty> getConnectionSettings() {
      if (connectionSettings == null) {
         connectionSettings = new EObjectContainmentEList<DbcProperty>(DbcProperty.class, this, DbcmodelPackage.DBC_MODEL__CONNECTION_SETTINGS);
      }
      return connectionSettings;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<DbcProofObligation> getProofObligations() {
      if (proofObligations == null) {
         proofObligations = new EObjectContainmentEList<DbcProofObligation>(DbcProofObligation.class, this, DbcmodelPackage.DBC_MODEL__PROOF_OBLIGATIONS);
      }
      return proofObligations;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated NOT
    */
   public Properties toConnectionProperties() {
      Properties result = new Properties();
      for (DbcProperty property : getConnectionSettings()) {
         result.setProperty(property.getKey(), property.getValue());
      }
      return result;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated NOT
    */
   public DbcProofObligation getProofObligation(String proofObligation) {
      DbcProofObligation result = null;
      Iterator<DbcProofObligation> iter = getProofObligations().iterator();
      while (result == null && iter.hasNext()) {
         DbcProofObligation next = iter.next();
         if (next.getObligation().equals(proofObligation)) {
            result = next;
         }
      }
      return result;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public NotificationChain eInverseRemove(InternalEObject otherEnd, int featureID, NotificationChain msgs) {
      switch (featureID) {
         case DbcmodelPackage.DBC_MODEL__CONNECTION_SETTINGS:
            return ((InternalEList<?>)getConnectionSettings()).basicRemove(otherEnd, msgs);
         case DbcmodelPackage.DBC_MODEL__PROOF_OBLIGATIONS:
            return ((InternalEList<?>)getProofObligations()).basicRemove(otherEnd, msgs);
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
         case DbcmodelPackage.DBC_MODEL__DRIVER_ID:
            return getDriverId();
         case DbcmodelPackage.DBC_MODEL__CONNECTION_SETTINGS:
            return getConnectionSettings();
         case DbcmodelPackage.DBC_MODEL__PROOF_OBLIGATIONS:
            return getProofObligations();
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
         case DbcmodelPackage.DBC_MODEL__DRIVER_ID:
            setDriverId((String)newValue);
            return;
         case DbcmodelPackage.DBC_MODEL__CONNECTION_SETTINGS:
            getConnectionSettings().clear();
            getConnectionSettings().addAll((Collection<? extends DbcProperty>)newValue);
            return;
         case DbcmodelPackage.DBC_MODEL__PROOF_OBLIGATIONS:
            getProofObligations().clear();
            getProofObligations().addAll((Collection<? extends DbcProofObligation>)newValue);
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
         case DbcmodelPackage.DBC_MODEL__DRIVER_ID:
            setDriverId(DRIVER_ID_EDEFAULT);
            return;
         case DbcmodelPackage.DBC_MODEL__CONNECTION_SETTINGS:
            getConnectionSettings().clear();
            return;
         case DbcmodelPackage.DBC_MODEL__PROOF_OBLIGATIONS:
            getProofObligations().clear();
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
         case DbcmodelPackage.DBC_MODEL__DRIVER_ID:
            return DRIVER_ID_EDEFAULT == null ? driverId != null : !DRIVER_ID_EDEFAULT.equals(driverId);
         case DbcmodelPackage.DBC_MODEL__CONNECTION_SETTINGS:
            return connectionSettings != null && !connectionSettings.isEmpty();
         case DbcmodelPackage.DBC_MODEL__PROOF_OBLIGATIONS:
            return proofObligations != null && !proofObligations.isEmpty();
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
      result.append(" (driverId: ");
      result.append(driverId);
      result.append(')');
      return result.toString();
   }

} //DbcModelImpl