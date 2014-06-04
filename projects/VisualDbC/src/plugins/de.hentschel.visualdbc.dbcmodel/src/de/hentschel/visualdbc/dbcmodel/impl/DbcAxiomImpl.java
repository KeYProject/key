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
import org.eclipse.emf.ecore.util.EObjectResolvingEList;
import org.eclipse.emf.ecore.util.InternalEList;

import de.hentschel.visualdbc.dbcmodel.AbstractDbcSpecification;
import de.hentschel.visualdbc.dbcmodel.DbCAxiomContract;
import de.hentschel.visualdbc.dbcmodel.DbcAxiom;
import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Dbc Axiom</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcAxiomImpl#getAllReferences <em>All References</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcAxiomImpl#getName <em>Name</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcAxiomImpl#getDefinition <em>Definition</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcAxiomImpl#getAxiomContracts <em>Axiom Contracts</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class DbcAxiomImpl extends EObjectImpl implements DbcAxiom {
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
    * The default value of the '{@link #getDefinition() <em>Definition</em>}' attribute.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @see #getDefinition()
    * @generated
    * @ordered
    */
    protected static final String DEFINITION_EDEFAULT = null;

    /**
    * The cached value of the '{@link #getDefinition() <em>Definition</em>}' attribute.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @see #getDefinition()
    * @generated
    * @ordered
    */
    protected String definition = DEFINITION_EDEFAULT;

    /**
    * The cached value of the '{@link #getAxiomContracts() <em>Axiom Contracts</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getAxiomContracts()
    * @generated
    * @ordered
    */
   protected EList<DbCAxiomContract> axiomContracts;

   /**
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    */
    protected DbcAxiomImpl() {
      super();
   }

    /**
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    */
    @Override
    protected EClass eStaticClass() {
      return DbcmodelPackage.Literals.DBC_AXIOM;
   }

    /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<DbcProofReference> getAllReferences() {
      if (allReferences == null) {
         allReferences = new EObjectResolvingEList<DbcProofReference>(DbcProofReference.class, this, DbcmodelPackage.DBC_AXIOM__ALL_REFERENCES);
      }
      return allReferences;
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
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DBC_AXIOM__NAME, oldName, name));
   }

    /**
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    */
    public String getDefinition() {
      return definition;
   }

    /**
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    */
    public void setDefinition(String newDefinition) {
      String oldDefinition = definition;
      definition = newDefinition;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DBC_AXIOM__DEFINITION, oldDefinition, definition));
   }

    /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<DbCAxiomContract> getAxiomContracts() {
      if (axiomContracts == null) {
         axiomContracts = new EObjectContainmentEList<DbCAxiomContract>(DbCAxiomContract.class, this, DbcmodelPackage.DBC_AXIOM__AXIOM_CONTRACTS);
      }
      return axiomContracts;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated NOT
    */
   public DbCAxiomContract getAxiomContract(String pre, String dep) {
      DbCAxiomContract result = null;
      Iterator<DbCAxiomContract> iter = getAxiomContracts().iterator();
      while (result == null && iter.hasNext()) {
         DbCAxiomContract next = iter.next();
         if (next.getPre().equals(pre) && next.getDep().equals(dep)) {
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
         case DbcmodelPackage.DBC_AXIOM__AXIOM_CONTRACTS:
            return ((InternalEList<?>)getAxiomContracts()).basicRemove(otherEnd, msgs);
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
         case DbcmodelPackage.DBC_AXIOM__ALL_REFERENCES:
            return getAllReferences();
         case DbcmodelPackage.DBC_AXIOM__NAME:
            return getName();
         case DbcmodelPackage.DBC_AXIOM__DEFINITION:
            return getDefinition();
         case DbcmodelPackage.DBC_AXIOM__AXIOM_CONTRACTS:
            return getAxiomContracts();
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
         case DbcmodelPackage.DBC_AXIOM__NAME:
            setName((String)newValue);
            return;
         case DbcmodelPackage.DBC_AXIOM__DEFINITION:
            setDefinition((String)newValue);
            return;
         case DbcmodelPackage.DBC_AXIOM__AXIOM_CONTRACTS:
            getAxiomContracts().clear();
            getAxiomContracts().addAll((Collection<? extends DbCAxiomContract>)newValue);
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
         case DbcmodelPackage.DBC_AXIOM__NAME:
            setName(NAME_EDEFAULT);
            return;
         case DbcmodelPackage.DBC_AXIOM__DEFINITION:
            setDefinition(DEFINITION_EDEFAULT);
            return;
         case DbcmodelPackage.DBC_AXIOM__AXIOM_CONTRACTS:
            getAxiomContracts().clear();
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
         case DbcmodelPackage.DBC_AXIOM__ALL_REFERENCES:
            return allReferences != null && !allReferences.isEmpty();
         case DbcmodelPackage.DBC_AXIOM__NAME:
            return NAME_EDEFAULT == null ? name != null : !NAME_EDEFAULT.equals(name);
         case DbcmodelPackage.DBC_AXIOM__DEFINITION:
            return DEFINITION_EDEFAULT == null ? definition != null : !DEFINITION_EDEFAULT.equals(definition);
         case DbcmodelPackage.DBC_AXIOM__AXIOM_CONTRACTS:
            return axiomContracts != null && !axiomContracts.isEmpty();
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
      if (baseClass == AbstractDbcSpecification.class) {
         switch (derivedFeatureID) {
            case DbcmodelPackage.DBC_AXIOM__NAME: return DbcmodelPackage.ABSTRACT_DBC_SPECIFICATION__NAME;
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
      if (baseClass == AbstractDbcSpecification.class) {
         switch (baseFeatureID) {
            case DbcmodelPackage.ABSTRACT_DBC_SPECIFICATION__NAME: return DbcmodelPackage.DBC_AXIOM__NAME;
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
      result.append(", definition: ");
      result.append(definition);
      result.append(')');
      return result.toString();
   }

} //DbcAxiomImpl