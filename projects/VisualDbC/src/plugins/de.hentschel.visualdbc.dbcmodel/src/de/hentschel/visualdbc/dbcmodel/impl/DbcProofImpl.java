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
import org.eclipse.emf.ecore.impl.EObjectImpl;
import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.InternalEList;

import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.DbcProofStatus;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
import de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable;
import de.hentschel.visualdbc.dbcmodel.IDbCProvable;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Dbc Proof</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcProofImpl#getTarget <em>Target</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcProofImpl#getProofReferences <em>Proof References</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcProofImpl#getObligation <em>Obligation</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcProofImpl#getStatus <em>Status</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class DbcProofImpl extends EObjectImpl implements DbcProof {
   /**
    * The cached value of the '{@link #getTarget() <em>Target</em>}' reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getTarget()
    * @generated
    * @ordered
    */
   protected IDbCProvable target;

   /**
    * The cached value of the '{@link #getProofReferences() <em>Proof References</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getProofReferences()
    * @generated
    * @ordered
    */
   protected EList<DbcProofReference> proofReferences;

   /**
    * The default value of the '{@link #getObligation() <em>Obligation</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getObligation()
    * @generated
    * @ordered
    */
   protected static final String OBLIGATION_EDEFAULT = null;

   /**
    * The cached value of the '{@link #getObligation() <em>Obligation</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getObligation()
    * @generated
    * @ordered
    */
   protected String obligation = OBLIGATION_EDEFAULT;

   /**
    * The default value of the '{@link #getStatus() <em>Status</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getStatus()
    * @generated
    * @ordered
    */
   protected static final DbcProofStatus STATUS_EDEFAULT = DbcProofStatus.OPEN;

   /**
    * The cached value of the '{@link #getStatus() <em>Status</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getStatus()
    * @generated
    * @ordered
    */
   protected DbcProofStatus status = STATUS_EDEFAULT;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected DbcProofImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return DbcmodelPackage.Literals.DBC_PROOF;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String getObligation() {
      return obligation;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setObligation(String newObligation) {
      String oldObligation = obligation;
      obligation = newObligation;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DBC_PROOF__OBLIGATION, oldObligation, obligation));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public IDbCProvable getTarget() {
      if (target != null && target.eIsProxy()) {
         InternalEObject oldTarget = (InternalEObject)target;
         target = (IDbCProvable)eResolveProxy(oldTarget);
         if (target != oldTarget) {
            if (eNotificationRequired())
               eNotify(new ENotificationImpl(this, Notification.RESOLVE, DbcmodelPackage.DBC_PROOF__TARGET, oldTarget, target));
         }
      }
      return target;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public IDbCProvable basicGetTarget() {
      return target;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated NOT
    */
   public void setTarget(IDbCProvable newTarget) {
      // Update references in provable
      if (target != null) {
         target.getAllProofs().remove(this);
      }
      if (newTarget != null) {
         newTarget.getAllProofs().add(this);
      }
      // Inform listers
      IDbCProvable oldTarget = target;
      target = newTarget;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DBC_PROOF__TARGET, oldTarget, target));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated NOT
    */
   public EList<DbcProofReference> getProofReferences() {
      if (proofReferences == null) {
         proofReferences = new EObjectContainmentEList<DbcProofReference>(DbcProofReference.class, this, DbcmodelPackage.DBC_PROOF__PROOF_REFERENCES) {
            /**
             * Generated UID.
             */
            private static final long serialVersionUID = 4638908045894728557L;

            @Override
            protected void didAdd(int index, DbcProofReference newObject) {
               super.didAdd(index, newObject);
               if (newObject != null) {
                  newObject.setSource(DbcProofImpl.this);
               }
            }

            @Override
            protected void didRemove(int index, DbcProofReference oldObject) {
               super.didRemove(index, oldObject);
               if (oldObject != null && oldObject.getSource() == DbcProofImpl.this) {
                  oldObject.setSource(null);
               }
            }
            
         };
      }
      return proofReferences;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcProofStatus getStatus() {
      return status;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setStatus(DbcProofStatus newStatus) {
      DbcProofStatus oldStatus = status;
      status = newStatus == null ? STATUS_EDEFAULT : newStatus;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DBC_PROOF__STATUS, oldStatus, status));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated NOT
    */
   public DbcProofReference getProofReference(IDbCProofReferencable target, String kind) {
      DbcProofReference result = null;
      Iterator<DbcProofReference> iter = getProofReferences().iterator();
      while (result == null && iter.hasNext()) {
         DbcProofReference next = iter.next();
         if (next.getTarget().equals(target) && next.getKind().equals(kind)) {
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
         case DbcmodelPackage.DBC_PROOF__PROOF_REFERENCES:
            return ((InternalEList<?>)getProofReferences()).basicRemove(otherEnd, msgs);
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
         case DbcmodelPackage.DBC_PROOF__TARGET:
            if (resolve) return getTarget();
            return basicGetTarget();
         case DbcmodelPackage.DBC_PROOF__PROOF_REFERENCES:
            return getProofReferences();
         case DbcmodelPackage.DBC_PROOF__OBLIGATION:
            return getObligation();
         case DbcmodelPackage.DBC_PROOF__STATUS:
            return getStatus();
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
         case DbcmodelPackage.DBC_PROOF__TARGET:
            setTarget((IDbCProvable)newValue);
            return;
         case DbcmodelPackage.DBC_PROOF__PROOF_REFERENCES:
            getProofReferences().clear();
            getProofReferences().addAll((Collection<? extends DbcProofReference>)newValue);
            return;
         case DbcmodelPackage.DBC_PROOF__OBLIGATION:
            setObligation((String)newValue);
            return;
         case DbcmodelPackage.DBC_PROOF__STATUS:
            setStatus((DbcProofStatus)newValue);
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
         case DbcmodelPackage.DBC_PROOF__TARGET:
            setTarget((IDbCProvable)null);
            return;
         case DbcmodelPackage.DBC_PROOF__PROOF_REFERENCES:
            getProofReferences().clear();
            return;
         case DbcmodelPackage.DBC_PROOF__OBLIGATION:
            setObligation(OBLIGATION_EDEFAULT);
            return;
         case DbcmodelPackage.DBC_PROOF__STATUS:
            setStatus(STATUS_EDEFAULT);
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
         case DbcmodelPackage.DBC_PROOF__TARGET:
            return target != null;
         case DbcmodelPackage.DBC_PROOF__PROOF_REFERENCES:
            return proofReferences != null && !proofReferences.isEmpty();
         case DbcmodelPackage.DBC_PROOF__OBLIGATION:
            return OBLIGATION_EDEFAULT == null ? obligation != null : !OBLIGATION_EDEFAULT.equals(obligation);
         case DbcmodelPackage.DBC_PROOF__STATUS:
            return status != STATUS_EDEFAULT;
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
      result.append(" (obligation: ");
      result.append(obligation);
      result.append(", status: ");
      result.append(status);
      result.append(')');
      return result.toString();
   }

} //DbcProofImpl