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

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.util.EObjectResolvingEList;

import de.hentschel.visualdbc.dbcmodel.DbcInvariant;
import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
import de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Dbc Invariant</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcInvariantImpl#getAllReferences <em>All References</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcInvariantImpl#getCondition <em>Condition</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class DbcInvariantImpl extends AbstractDbcSpecificationImpl implements DbcInvariant {
   /**
    * The cached value of the '{@link #getAllReferences() <em>All References</em>}' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getAllReferences()
    * @generated
    * @ordered
    */
   protected EList<DbcProofReference> allReferences;

   /**
    * The default value of the '{@link #getCondition() <em>Condition</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getCondition()
    * @generated
    * @ordered
    */
   protected static final String CONDITION_EDEFAULT = null;

   /**
    * The cached value of the '{@link #getCondition() <em>Condition</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getCondition()
    * @generated
    * @ordered
    */
   protected String condition = CONDITION_EDEFAULT;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected DbcInvariantImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return DbcmodelPackage.Literals.DBC_INVARIANT;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<DbcProofReference> getAllReferences() {
      if (allReferences == null) {
         allReferences = new EObjectResolvingEList<DbcProofReference>(DbcProofReference.class, this, DbcmodelPackage.DBC_INVARIANT__ALL_REFERENCES);
      }
      return allReferences;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String getCondition() {
      return condition;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setCondition(String newCondition) {
      String oldCondition = condition;
      condition = newCondition;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DBC_INVARIANT__CONDITION, oldCondition, condition));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public Object eGet(int featureID, boolean resolve, boolean coreType) {
      switch (featureID) {
         case DbcmodelPackage.DBC_INVARIANT__ALL_REFERENCES:
            return getAllReferences();
         case DbcmodelPackage.DBC_INVARIANT__CONDITION:
            return getCondition();
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
         case DbcmodelPackage.DBC_INVARIANT__CONDITION:
            setCondition((String)newValue);
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
         case DbcmodelPackage.DBC_INVARIANT__CONDITION:
            setCondition(CONDITION_EDEFAULT);
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
         case DbcmodelPackage.DBC_INVARIANT__ALL_REFERENCES:
            return allReferences != null && !allReferences.isEmpty();
         case DbcmodelPackage.DBC_INVARIANT__CONDITION:
            return CONDITION_EDEFAULT == null ? condition != null : !CONDITION_EDEFAULT.equals(condition);
      }
      return super.eIsSet(featureID);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public int eBaseStructuralFeatureID(int derivedFeatureID, Class<?> baseClass) {
      if (baseClass == IDbCProofReferencable.class) {
         switch (derivedFeatureID) {
            case DbcmodelPackage.DBC_INVARIANT__ALL_REFERENCES: return DbcmodelPackage.IDB_CPROOF_REFERENCABLE__ALL_REFERENCES;
            default: return -1;
         }
      }
      return super.eBaseStructuralFeatureID(derivedFeatureID, baseClass);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public int eDerivedStructuralFeatureID(int baseFeatureID, Class<?> baseClass) {
      if (baseClass == IDbCProofReferencable.class) {
         switch (baseFeatureID) {
            case DbcmodelPackage.IDB_CPROOF_REFERENCABLE__ALL_REFERENCES: return DbcmodelPackage.DBC_INVARIANT__ALL_REFERENCES;
            default: return -1;
         }
      }
      return super.eDerivedStructuralFeatureID(baseFeatureID, baseClass);
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
      result.append(" (condition: ");
      result.append(condition);
      result.append(')');
      return result.toString();
   }

} //DbcInvariantImpl