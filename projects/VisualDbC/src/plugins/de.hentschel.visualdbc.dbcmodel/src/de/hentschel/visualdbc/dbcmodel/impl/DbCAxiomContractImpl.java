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

import de.hentschel.visualdbc.dbcmodel.DbCAxiomContract;
import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofObligation;
import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
import de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable;
import de.hentschel.visualdbc.dbcmodel.IDbCProvable;

import java.util.Collection;

import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

import org.eclipse.emf.ecore.util.EObjectResolvingEList;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Db CAxiom Contract</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbCAxiomContractImpl#getAllReferences <em>All References</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbCAxiomContractImpl#getProofObligations <em>Proof Obligations</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbCAxiomContractImpl#getAllProofs <em>All Proofs</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbCAxiomContractImpl#getPre <em>Pre</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbCAxiomContractImpl#getDep <em>Dep</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class DbCAxiomContractImpl extends AbstractDbcSpecificationImpl implements DbCAxiomContract {
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
    * The default value of the '{@link #getPre() <em>Pre</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getPre()
    * @generated
    * @ordered
    */
   protected static final String PRE_EDEFAULT = null;

   /**
    * The cached value of the '{@link #getPre() <em>Pre</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getPre()
    * @generated
    * @ordered
    */
   protected String pre = PRE_EDEFAULT;

   /**
    * The default value of the '{@link #getDep() <em>Dep</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getDep()
    * @generated
    * @ordered
    */
   protected static final String DEP_EDEFAULT = null;

   /**
    * The cached value of the '{@link #getDep() <em>Dep</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getDep()
    * @generated
    * @ordered
    */
   protected String dep = DEP_EDEFAULT;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected DbCAxiomContractImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return DbcmodelPackage.Literals.DB_CAXIOM_CONTRACT;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<DbcProofReference> getAllReferences() {
      if (allReferences == null) {
         allReferences = new EObjectResolvingEList<DbcProofReference>(DbcProofReference.class, this, DbcmodelPackage.DB_CAXIOM_CONTRACT__ALL_REFERENCES);
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
         proofObligations = new EObjectResolvingEList<DbcProofObligation>(DbcProofObligation.class, this, DbcmodelPackage.DB_CAXIOM_CONTRACT__PROOF_OBLIGATIONS);
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
         allProofs = new EObjectResolvingEList<DbcProof>(DbcProof.class, this, DbcmodelPackage.DB_CAXIOM_CONTRACT__ALL_PROOFS);
      }
      return allProofs;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String getPre() {
      return pre;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setPre(String newPre) {
      String oldPre = pre;
      pre = newPre;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DB_CAXIOM_CONTRACT__PRE, oldPre, pre));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String getDep() {
      return dep;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setDep(String newDep) {
      String oldDep = dep;
      dep = newDep;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DB_CAXIOM_CONTRACT__DEP, oldDep, dep));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public Object eGet(int featureID, boolean resolve, boolean coreType) {
      switch (featureID) {
         case DbcmodelPackage.DB_CAXIOM_CONTRACT__ALL_REFERENCES:
            return getAllReferences();
         case DbcmodelPackage.DB_CAXIOM_CONTRACT__PROOF_OBLIGATIONS:
            return getProofObligations();
         case DbcmodelPackage.DB_CAXIOM_CONTRACT__ALL_PROOFS:
            return getAllProofs();
         case DbcmodelPackage.DB_CAXIOM_CONTRACT__PRE:
            return getPre();
         case DbcmodelPackage.DB_CAXIOM_CONTRACT__DEP:
            return getDep();
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
         case DbcmodelPackage.DB_CAXIOM_CONTRACT__PROOF_OBLIGATIONS:
            getProofObligations().clear();
            getProofObligations().addAll((Collection<? extends DbcProofObligation>)newValue);
            return;
         case DbcmodelPackage.DB_CAXIOM_CONTRACT__PRE:
            setPre((String)newValue);
            return;
         case DbcmodelPackage.DB_CAXIOM_CONTRACT__DEP:
            setDep((String)newValue);
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
         case DbcmodelPackage.DB_CAXIOM_CONTRACT__PROOF_OBLIGATIONS:
            getProofObligations().clear();
            return;
         case DbcmodelPackage.DB_CAXIOM_CONTRACT__PRE:
            setPre(PRE_EDEFAULT);
            return;
         case DbcmodelPackage.DB_CAXIOM_CONTRACT__DEP:
            setDep(DEP_EDEFAULT);
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
         case DbcmodelPackage.DB_CAXIOM_CONTRACT__ALL_REFERENCES:
            return allReferences != null && !allReferences.isEmpty();
         case DbcmodelPackage.DB_CAXIOM_CONTRACT__PROOF_OBLIGATIONS:
            return proofObligations != null && !proofObligations.isEmpty();
         case DbcmodelPackage.DB_CAXIOM_CONTRACT__ALL_PROOFS:
            return allProofs != null && !allProofs.isEmpty();
         case DbcmodelPackage.DB_CAXIOM_CONTRACT__PRE:
            return PRE_EDEFAULT == null ? pre != null : !PRE_EDEFAULT.equals(pre);
         case DbcmodelPackage.DB_CAXIOM_CONTRACT__DEP:
            return DEP_EDEFAULT == null ? dep != null : !DEP_EDEFAULT.equals(dep);
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
            case DbcmodelPackage.DB_CAXIOM_CONTRACT__ALL_REFERENCES: return DbcmodelPackage.IDB_CPROOF_REFERENCABLE__ALL_REFERENCES;
            default: return -1;
         }
      }
      if (baseClass == IDbCProvable.class) {
         switch (derivedFeatureID) {
            case DbcmodelPackage.DB_CAXIOM_CONTRACT__PROOF_OBLIGATIONS: return DbcmodelPackage.IDB_CPROVABLE__PROOF_OBLIGATIONS;
            case DbcmodelPackage.DB_CAXIOM_CONTRACT__ALL_PROOFS: return DbcmodelPackage.IDB_CPROVABLE__ALL_PROOFS;
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
            case DbcmodelPackage.IDB_CPROOF_REFERENCABLE__ALL_REFERENCES: return DbcmodelPackage.DB_CAXIOM_CONTRACT__ALL_REFERENCES;
            default: return -1;
         }
      }
      if (baseClass == IDbCProvable.class) {
         switch (baseFeatureID) {
            case DbcmodelPackage.IDB_CPROVABLE__PROOF_OBLIGATIONS: return DbcmodelPackage.DB_CAXIOM_CONTRACT__PROOF_OBLIGATIONS;
            case DbcmodelPackage.IDB_CPROVABLE__ALL_PROOFS: return DbcmodelPackage.DB_CAXIOM_CONTRACT__ALL_PROOFS;
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
      result.append(" (pre: ");
      result.append(pre);
      result.append(", dep: ");
      result.append(dep);
      result.append(')');
      return result.toString();
   }

} //DbCAxiomContractImpl