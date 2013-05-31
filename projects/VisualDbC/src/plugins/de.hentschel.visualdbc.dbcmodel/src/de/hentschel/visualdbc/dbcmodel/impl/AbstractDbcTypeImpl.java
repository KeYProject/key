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

import de.hentschel.visualdbc.dbcmodel.AbstractDbcType;
import de.hentschel.visualdbc.dbcmodel.DbcAxiom;
import de.hentschel.visualdbc.dbcmodel.DbcInvariant;
import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofObligation;
import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.DbcVisibility;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
import de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable;
import de.hentschel.visualdbc.dbcmodel.IDbCProvable;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Abstract Dbc Type</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcTypeImpl#getAllReferences <em>All References</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcTypeImpl#getProofObligations <em>Proof Obligations</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcTypeImpl#getAllProofs <em>All Proofs</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcTypeImpl#getName <em>Name</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcTypeImpl#getVisibility <em>Visibility</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcTypeImpl#isStatic <em>Static</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcTypeImpl#getInvariants <em>Invariants</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcTypeImpl#getAxioms <em>Axioms</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public abstract class AbstractDbcTypeImpl extends AbstractDbcTypeContainerImpl implements AbstractDbcType {
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
    * The cached value of the '{@link #getInvariants() <em>Invariants</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getInvariants()
    * @generated
    * @ordered
    */
   protected EList<DbcInvariant> invariants;

   /**
    * The cached value of the '{@link #getAxioms() <em>Axioms</em>}' containment reference list.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @see #getAxioms()
    * @generated
    * @ordered
    */
    protected EList<DbcAxiom> axioms;

/**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected AbstractDbcTypeImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return DbcmodelPackage.Literals.ABSTRACT_DBC_TYPE;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<DbcProofReference> getAllReferences() {
      if (allReferences == null) {
         allReferences = new EObjectResolvingEList<DbcProofReference>(DbcProofReference.class, this, DbcmodelPackage.ABSTRACT_DBC_TYPE__ALL_REFERENCES);
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
         proofObligations = new EObjectResolvingEList<DbcProofObligation>(DbcProofObligation.class, this, DbcmodelPackage.ABSTRACT_DBC_TYPE__PROOF_OBLIGATIONS);
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
         allProofs = new EObjectResolvingEList<DbcProof>(DbcProof.class, this, DbcmodelPackage.ABSTRACT_DBC_TYPE__ALL_PROOFS);
      }
      return allProofs;
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
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.ABSTRACT_DBC_TYPE__NAME, oldName, name));
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
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.ABSTRACT_DBC_TYPE__VISIBILITY, oldVisibility, visibility));
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
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.ABSTRACT_DBC_TYPE__STATIC, oldStatic, static_));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<DbcInvariant> getInvariants() {
      if (invariants == null) {
         invariants = new EObjectContainmentEList<DbcInvariant>(DbcInvariant.class, this, DbcmodelPackage.ABSTRACT_DBC_TYPE__INVARIANTS);
      }
      return invariants;
   }

   /**
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    */
    public EList<DbcAxiom> getAxioms() {
      if (axioms == null) {
         axioms = new EObjectContainmentEList<DbcAxiom>(DbcAxiom.class, this, DbcmodelPackage.ABSTRACT_DBC_TYPE__AXIOMS);
      }
      return axioms;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated NOT
    */
   public DbcInvariant getInvariant(String text) {
      DbcInvariant result = null;
      Iterator<DbcInvariant> iter = getInvariants().iterator();
      while (result == null && iter.hasNext()) {
         DbcInvariant next = iter.next();
         if (next.getCondition().equals(text)) {
            result = next;
         }
      }
      return result;
   }

   /**
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated NOT
     */
    public DbcAxiom getAxiom(String definition) {
       DbcAxiom result = null;
        Iterator<DbcAxiom> iter = getAxioms().iterator();
        while (result == null && iter.hasNext()) {
           DbcAxiom next = iter.next();
           if (next.getDefinition().equals(definition)) {
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
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__INVARIANTS:
            return ((InternalEList<?>)getInvariants()).basicRemove(otherEnd, msgs);
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__AXIOMS:
            return ((InternalEList<?>)getAxioms()).basicRemove(otherEnd, msgs);
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
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__ALL_REFERENCES:
            return getAllReferences();
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__PROOF_OBLIGATIONS:
            return getProofObligations();
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__ALL_PROOFS:
            return getAllProofs();
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__NAME:
            return getName();
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__VISIBILITY:
            return getVisibility();
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__STATIC:
            return isStatic();
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__INVARIANTS:
            return getInvariants();
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__AXIOMS:
            return getAxioms();
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
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__PROOF_OBLIGATIONS:
            getProofObligations().clear();
            getProofObligations().addAll((Collection<? extends DbcProofObligation>)newValue);
            return;
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__NAME:
            setName((String)newValue);
            return;
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__VISIBILITY:
            setVisibility((DbcVisibility)newValue);
            return;
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__STATIC:
            setStatic((Boolean)newValue);
            return;
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__INVARIANTS:
            getInvariants().clear();
            getInvariants().addAll((Collection<? extends DbcInvariant>)newValue);
            return;
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__AXIOMS:
            getAxioms().clear();
            getAxioms().addAll((Collection<? extends DbcAxiom>)newValue);
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
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__PROOF_OBLIGATIONS:
            getProofObligations().clear();
            return;
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__NAME:
            setName(NAME_EDEFAULT);
            return;
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__VISIBILITY:
            setVisibility(VISIBILITY_EDEFAULT);
            return;
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__STATIC:
            setStatic(STATIC_EDEFAULT);
            return;
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__INVARIANTS:
            getInvariants().clear();
            return;
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__AXIOMS:
            getAxioms().clear();
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
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__ALL_REFERENCES:
            return allReferences != null && !allReferences.isEmpty();
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__PROOF_OBLIGATIONS:
            return proofObligations != null && !proofObligations.isEmpty();
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__ALL_PROOFS:
            return allProofs != null && !allProofs.isEmpty();
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__NAME:
            return NAME_EDEFAULT == null ? name != null : !NAME_EDEFAULT.equals(name);
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__VISIBILITY:
            return visibility != VISIBILITY_EDEFAULT;
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__STATIC:
            return static_ != STATIC_EDEFAULT;
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__INVARIANTS:
            return invariants != null && !invariants.isEmpty();
         case DbcmodelPackage.ABSTRACT_DBC_TYPE__AXIOMS:
            return axioms != null && !axioms.isEmpty();
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
            case DbcmodelPackage.ABSTRACT_DBC_TYPE__ALL_REFERENCES: return DbcmodelPackage.IDB_CPROOF_REFERENCABLE__ALL_REFERENCES;
            default: return -1;
         }
      }
      if (baseClass == IDbCProvable.class) {
         switch (derivedFeatureID) {
            case DbcmodelPackage.ABSTRACT_DBC_TYPE__PROOF_OBLIGATIONS: return DbcmodelPackage.IDB_CPROVABLE__PROOF_OBLIGATIONS;
            case DbcmodelPackage.ABSTRACT_DBC_TYPE__ALL_PROOFS: return DbcmodelPackage.IDB_CPROVABLE__ALL_PROOFS;
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
            case DbcmodelPackage.IDB_CPROOF_REFERENCABLE__ALL_REFERENCES: return DbcmodelPackage.ABSTRACT_DBC_TYPE__ALL_REFERENCES;
            default: return -1;
         }
      }
      if (baseClass == IDbCProvable.class) {
         switch (baseFeatureID) {
            case DbcmodelPackage.IDB_CPROVABLE__PROOF_OBLIGATIONS: return DbcmodelPackage.ABSTRACT_DBC_TYPE__PROOF_OBLIGATIONS;
            case DbcmodelPackage.IDB_CPROVABLE__ALL_PROOFS: return DbcmodelPackage.ABSTRACT_DBC_TYPE__ALL_PROOFS;
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
      result.append(" (name: ");
      result.append(name);
      result.append(", visibility: ");
      result.append(visibility);
      result.append(", static: ");
      result.append(static_);
      result.append(')');
      return result.toString();
   }

} //AbstractDbcTypeImpl