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

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.util.EObjectResolvingEList;

import de.hentschel.visualdbc.dbcmodel.DbcOperationContract;
import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofObligation;
import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
import de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable;
import de.hentschel.visualdbc.dbcmodel.IDbCProvable;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Dbc Operation Contract</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcOperationContractImpl#getAllReferences <em>All References</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcOperationContractImpl#getProofObligations <em>Proof Obligations</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcOperationContractImpl#getAllProofs <em>All Proofs</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcOperationContractImpl#getPre <em>Pre</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcOperationContractImpl#getPost <em>Post</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcOperationContractImpl#getModifies <em>Modifies</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcOperationContractImpl#getTermination <em>Termination</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class DbcOperationContractImpl extends AbstractDbcSpecificationImpl implements DbcOperationContract {
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
    * The default value of the '{@link #getPost() <em>Post</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getPost()
    * @generated
    * @ordered
    */
   protected static final String POST_EDEFAULT = null;

   /**
    * The cached value of the '{@link #getPost() <em>Post</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getPost()
    * @generated
    * @ordered
    */
   protected String post = POST_EDEFAULT;

   /**
    * The default value of the '{@link #getModifies() <em>Modifies</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getModifies()
    * @generated
    * @ordered
    */
   protected static final String MODIFIES_EDEFAULT = null;

   /**
    * The cached value of the '{@link #getModifies() <em>Modifies</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getModifies()
    * @generated
    * @ordered
    */
   protected String modifies = MODIFIES_EDEFAULT;

   /**
    * The default value of the '{@link #getTermination() <em>Termination</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getTermination()
    * @generated
    * @ordered
    */
   protected static final String TERMINATION_EDEFAULT = null;

   /**
    * The cached value of the '{@link #getTermination() <em>Termination</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getTermination()
    * @generated
    * @ordered
    */
   protected String termination = TERMINATION_EDEFAULT;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected DbcOperationContractImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return DbcmodelPackage.Literals.DBC_OPERATION_CONTRACT;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<DbcProofReference> getAllReferences() {
      if (allReferences == null) {
         allReferences = new EObjectResolvingEList<DbcProofReference>(DbcProofReference.class, this, DbcmodelPackage.DBC_OPERATION_CONTRACT__ALL_REFERENCES);
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
         proofObligations = new EObjectResolvingEList<DbcProofObligation>(DbcProofObligation.class, this, DbcmodelPackage.DBC_OPERATION_CONTRACT__PROOF_OBLIGATIONS);
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
         allProofs = new EObjectResolvingEList<DbcProof>(DbcProof.class, this, DbcmodelPackage.DBC_OPERATION_CONTRACT__ALL_PROOFS);
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
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DBC_OPERATION_CONTRACT__PRE, oldPre, pre));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String getPost() {
      return post;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setPost(String newPost) {
      String oldPost = post;
      post = newPost;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DBC_OPERATION_CONTRACT__POST, oldPost, post));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String getModifies() {
      return modifies;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setModifies(String newModifies) {
      String oldModifies = modifies;
      modifies = newModifies;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DBC_OPERATION_CONTRACT__MODIFIES, oldModifies, modifies));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String getTermination() {
      return termination;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setTermination(String newTermination) {
      String oldTermination = termination;
      termination = newTermination;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DBC_OPERATION_CONTRACT__TERMINATION, oldTermination, termination));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public Object eGet(int featureID, boolean resolve, boolean coreType) {
      switch (featureID) {
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__ALL_REFERENCES:
            return getAllReferences();
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__PROOF_OBLIGATIONS:
            return getProofObligations();
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__ALL_PROOFS:
            return getAllProofs();
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__PRE:
            return getPre();
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__POST:
            return getPost();
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__MODIFIES:
            return getModifies();
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__TERMINATION:
            return getTermination();
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
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__PROOF_OBLIGATIONS:
            getProofObligations().clear();
            getProofObligations().addAll((Collection<? extends DbcProofObligation>)newValue);
            return;
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__PRE:
            setPre((String)newValue);
            return;
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__POST:
            setPost((String)newValue);
            return;
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__MODIFIES:
            setModifies((String)newValue);
            return;
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__TERMINATION:
            setTermination((String)newValue);
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
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__PROOF_OBLIGATIONS:
            getProofObligations().clear();
            return;
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__PRE:
            setPre(PRE_EDEFAULT);
            return;
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__POST:
            setPost(POST_EDEFAULT);
            return;
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__MODIFIES:
            setModifies(MODIFIES_EDEFAULT);
            return;
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__TERMINATION:
            setTermination(TERMINATION_EDEFAULT);
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
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__ALL_REFERENCES:
            return allReferences != null && !allReferences.isEmpty();
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__PROOF_OBLIGATIONS:
            return proofObligations != null && !proofObligations.isEmpty();
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__ALL_PROOFS:
            return allProofs != null && !allProofs.isEmpty();
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__PRE:
            return PRE_EDEFAULT == null ? pre != null : !PRE_EDEFAULT.equals(pre);
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__POST:
            return POST_EDEFAULT == null ? post != null : !POST_EDEFAULT.equals(post);
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__MODIFIES:
            return MODIFIES_EDEFAULT == null ? modifies != null : !MODIFIES_EDEFAULT.equals(modifies);
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__TERMINATION:
            return TERMINATION_EDEFAULT == null ? termination != null : !TERMINATION_EDEFAULT.equals(termination);
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
            case DbcmodelPackage.DBC_OPERATION_CONTRACT__ALL_REFERENCES: return DbcmodelPackage.IDB_CPROOF_REFERENCABLE__ALL_REFERENCES;
            default: return -1;
         }
      }
      if (baseClass == IDbCProvable.class) {
         switch (derivedFeatureID) {
            case DbcmodelPackage.DBC_OPERATION_CONTRACT__PROOF_OBLIGATIONS: return DbcmodelPackage.IDB_CPROVABLE__PROOF_OBLIGATIONS;
            case DbcmodelPackage.DBC_OPERATION_CONTRACT__ALL_PROOFS: return DbcmodelPackage.IDB_CPROVABLE__ALL_PROOFS;
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
            case DbcmodelPackage.IDB_CPROOF_REFERENCABLE__ALL_REFERENCES: return DbcmodelPackage.DBC_OPERATION_CONTRACT__ALL_REFERENCES;
            default: return -1;
         }
      }
      if (baseClass == IDbCProvable.class) {
         switch (baseFeatureID) {
            case DbcmodelPackage.IDB_CPROVABLE__PROOF_OBLIGATIONS: return DbcmodelPackage.DBC_OPERATION_CONTRACT__PROOF_OBLIGATIONS;
            case DbcmodelPackage.IDB_CPROVABLE__ALL_PROOFS: return DbcmodelPackage.DBC_OPERATION_CONTRACT__ALL_PROOFS;
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
      result.append(", post: ");
      result.append(post);
      result.append(", modifies: ");
      result.append(modifies);
      result.append(", termination: ");
      result.append(termination);
      result.append(')');
      return result.toString();
   }

} //DbcOperationContractImpl