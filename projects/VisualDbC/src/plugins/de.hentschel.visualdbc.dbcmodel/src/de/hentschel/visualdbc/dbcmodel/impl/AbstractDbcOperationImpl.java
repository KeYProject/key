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

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.NotificationChain;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;
import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.EObjectResolvingEList;
import org.eclipse.emf.ecore.util.InternalEList;

import de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation;
import de.hentschel.visualdbc.dbcmodel.DbcOperationContract;
import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofObligation;
import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.DbcVisibility;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
import de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable;
import de.hentschel.visualdbc.dbcmodel.IDbCProvable;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Abstract Dbc Operation</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcOperationImpl#getAllReferences <em>All References</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcOperationImpl#getProofObligations <em>Proof Obligations</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcOperationImpl#getAllProofs <em>All Proofs</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcOperationImpl#getOperationContracts <em>Operation Contracts</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcOperationImpl#getSignature <em>Signature</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcOperationImpl#getVisibility <em>Visibility</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcOperationImpl#isStatic <em>Static</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public abstract class AbstractDbcOperationImpl extends AbstractDbcProofContainerImpl implements AbstractDbcOperation {
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
    * The cached value of the '{@link #getProofObligations() <em>Proof Obligations</em>}' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getProofObligations()
    * @generated
    * @ordered
    */
   protected EList<DbcProofObligation> proofObligations;

   /**
    * The cached value of the '{@link #getAllProofs() <em>All Proofs</em>}' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getAllProofs()
    * @generated
    * @ordered
    */
   protected EList<DbcProof> allProofs;

   /**
    * The cached value of the '{@link #getOperationContracts() <em>Operation Contracts</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getOperationContracts()
    * @generated
    * @ordered
    */
   protected EList<DbcOperationContract> operationContracts;

   /**
    * The default value of the '{@link #getSignature() <em>Signature</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getSignature()
    * @generated
    * @ordered
    */
   protected static final String SIGNATURE_EDEFAULT = null;
   /**
    * The cached value of the '{@link #getSignature() <em>Signature</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getSignature()
    * @generated
    * @ordered
    */
   protected String signature = SIGNATURE_EDEFAULT;
   /**
    * The default value of the '{@link #getVisibility() <em>Visibility</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getVisibility()
    * @generated
    * @ordered
    */
   protected static final DbcVisibility VISIBILITY_EDEFAULT = DbcVisibility.PUBLIC;
   /**
    * The cached value of the '{@link #getVisibility() <em>Visibility</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getVisibility()
    * @generated
    * @ordered
    */
   protected DbcVisibility visibility = VISIBILITY_EDEFAULT;
   /**
    * The default value of the '{@link #isStatic() <em>Static</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #isStatic()
    * @generated
    * @ordered
    */
   protected static final boolean STATIC_EDEFAULT = false;
   /**
    * The cached value of the '{@link #isStatic() <em>Static</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #isStatic()
    * @generated
    * @ordered
    */
   protected boolean static_ = STATIC_EDEFAULT;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected AbstractDbcOperationImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return DbcmodelPackage.Literals.ABSTRACT_DBC_OPERATION;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<DbcProofReference> getAllReferences() {
      if (allReferences == null) {
         allReferences = new EObjectResolvingEList<DbcProofReference>(DbcProofReference.class, this, DbcmodelPackage.ABSTRACT_DBC_OPERATION__ALL_REFERENCES);
      }
      return allReferences;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<DbcProofObligation> getProofObligations() {
      if (proofObligations == null) {
         proofObligations = new EObjectResolvingEList<DbcProofObligation>(DbcProofObligation.class, this, DbcmodelPackage.ABSTRACT_DBC_OPERATION__PROOF_OBLIGATIONS);
      }
      return proofObligations;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<DbcProof> getAllProofs() {
      if (allProofs == null) {
         allProofs = new EObjectResolvingEList<DbcProof>(DbcProof.class, this, DbcmodelPackage.ABSTRACT_DBC_OPERATION__ALL_PROOFS);
      }
      return allProofs;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<DbcOperationContract> getOperationContracts() {
      if (operationContracts == null) {
         operationContracts = new EObjectContainmentEList<DbcOperationContract>(DbcOperationContract.class, this, DbcmodelPackage.ABSTRACT_DBC_OPERATION__OPERATION_CONTRACTS);
      }
      return operationContracts;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String getSignature() {
      return signature;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setSignature(String newSignature) {
      String oldSignature = signature;
      signature = newSignature;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.ABSTRACT_DBC_OPERATION__SIGNATURE, oldSignature, signature));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcVisibility getVisibility() {
      return visibility;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setVisibility(DbcVisibility newVisibility) {
      DbcVisibility oldVisibility = visibility;
      visibility = newVisibility == null ? VISIBILITY_EDEFAULT : newVisibility;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.ABSTRACT_DBC_OPERATION__VISIBILITY, oldVisibility, visibility));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public boolean isStatic() {
      return static_;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setStatic(boolean newStatic) {
      boolean oldStatic = static_;
      static_ = newStatic;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.ABSTRACT_DBC_OPERATION__STATIC, oldStatic, static_));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated NOT
    */
   public DbcOperationContract getOperationContract(String pre, String post) {
      DbcOperationContract result = null;
      Iterator<DbcOperationContract> iter = getOperationContracts().iterator();
      while (result == null && iter.hasNext()) {
         DbcOperationContract next = iter.next();
         if (next.getPre().equals(pre) && next.getPost().equals(post)) {
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
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__OPERATION_CONTRACTS:
            return ((InternalEList<?>)getOperationContracts()).basicRemove(otherEnd, msgs);
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
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__ALL_REFERENCES:
            return getAllReferences();
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__PROOF_OBLIGATIONS:
            return getProofObligations();
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__ALL_PROOFS:
            return getAllProofs();
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__OPERATION_CONTRACTS:
            return getOperationContracts();
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__SIGNATURE:
            return getSignature();
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__VISIBILITY:
            return getVisibility();
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__STATIC:
            return isStatic();
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
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__PROOF_OBLIGATIONS:
            getProofObligations().clear();
            getProofObligations().addAll((Collection<? extends DbcProofObligation>)newValue);
            return;
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__OPERATION_CONTRACTS:
            getOperationContracts().clear();
            getOperationContracts().addAll((Collection<? extends DbcOperationContract>)newValue);
            return;
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__SIGNATURE:
            setSignature((String)newValue);
            return;
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__VISIBILITY:
            setVisibility((DbcVisibility)newValue);
            return;
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__STATIC:
            setStatic((Boolean)newValue);
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
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__PROOF_OBLIGATIONS:
            getProofObligations().clear();
            return;
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__OPERATION_CONTRACTS:
            getOperationContracts().clear();
            return;
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__SIGNATURE:
            setSignature(SIGNATURE_EDEFAULT);
            return;
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__VISIBILITY:
            setVisibility(VISIBILITY_EDEFAULT);
            return;
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__STATIC:
            setStatic(STATIC_EDEFAULT);
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
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__ALL_REFERENCES:
            return allReferences != null && !allReferences.isEmpty();
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__PROOF_OBLIGATIONS:
            return proofObligations != null && !proofObligations.isEmpty();
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__ALL_PROOFS:
            return allProofs != null && !allProofs.isEmpty();
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__OPERATION_CONTRACTS:
            return operationContracts != null && !operationContracts.isEmpty();
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__SIGNATURE:
            return SIGNATURE_EDEFAULT == null ? signature != null : !SIGNATURE_EDEFAULT.equals(signature);
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__VISIBILITY:
            return visibility != VISIBILITY_EDEFAULT;
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION__STATIC:
            return static_ != STATIC_EDEFAULT;
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
            case DbcmodelPackage.ABSTRACT_DBC_OPERATION__ALL_REFERENCES: return DbcmodelPackage.IDB_CPROOF_REFERENCABLE__ALL_REFERENCES;
            default: return -1;
         }
      }
      if (baseClass == IDbCProvable.class) {
         switch (derivedFeatureID) {
            case DbcmodelPackage.ABSTRACT_DBC_OPERATION__PROOF_OBLIGATIONS: return DbcmodelPackage.IDB_CPROVABLE__PROOF_OBLIGATIONS;
            case DbcmodelPackage.ABSTRACT_DBC_OPERATION__ALL_PROOFS: return DbcmodelPackage.IDB_CPROVABLE__ALL_PROOFS;
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
            case DbcmodelPackage.IDB_CPROOF_REFERENCABLE__ALL_REFERENCES: return DbcmodelPackage.ABSTRACT_DBC_OPERATION__ALL_REFERENCES;
            default: return -1;
         }
      }
      if (baseClass == IDbCProvable.class) {
         switch (baseFeatureID) {
            case DbcmodelPackage.IDB_CPROVABLE__PROOF_OBLIGATIONS: return DbcmodelPackage.ABSTRACT_DBC_OPERATION__PROOF_OBLIGATIONS;
            case DbcmodelPackage.IDB_CPROVABLE__ALL_PROOFS: return DbcmodelPackage.ABSTRACT_DBC_OPERATION__ALL_PROOFS;
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
      result.append(" (signature: ");
      result.append(signature);
      result.append(", visibility: ");
      result.append(visibility);
      result.append(", static: ");
      result.append(static_);
      result.append(')');
      return result.toString();
   }

} //AbstractDbcOperationImpl