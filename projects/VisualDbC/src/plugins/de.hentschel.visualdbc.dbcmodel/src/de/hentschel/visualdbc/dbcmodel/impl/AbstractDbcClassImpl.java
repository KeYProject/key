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

import org.eclipse.emf.common.notify.NotificationChain;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;
import org.eclipse.emf.ecore.util.EDataTypeUniqueEList;
import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.EObjectResolvingEList;
import org.eclipse.emf.ecore.util.InternalEList;

import de.hentschel.visualdbc.dbcmodel.AbstractDbcClass;
import de.hentschel.visualdbc.dbcmodel.DbcConstructor;
import de.hentschel.visualdbc.dbcmodel.DbcInterface;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Abstract Dbc Class</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcClassImpl#getConstructors <em>Constructors</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcClassImpl#getImplements <em>Implements</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcClassImpl#getImplementsFullNames <em>Implements Full Names</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public abstract class AbstractDbcClassImpl extends AbstractDbcInterfaceImpl implements AbstractDbcClass {
   /**
    * The cached value of the '{@link #getConstructors() <em>Constructors</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getConstructors()
    * @generated
    * @ordered
    */
   protected EList<DbcConstructor> constructors;

   /**
    * The cached value of the '{@link #getImplements() <em>Implements</em>}' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getImplements()
    * @generated
    * @ordered
    */
   protected EList<DbcInterface> implements_;

   /**
    * The cached value of the '{@link #getImplementsFullNames() <em>Implements Full Names</em>}' attribute list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getImplementsFullNames()
    * @generated
    * @ordered
    */
   protected EList<String> implementsFullNames;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected AbstractDbcClassImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return DbcmodelPackage.Literals.ABSTRACT_DBC_CLASS;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<DbcConstructor> getConstructors() {
      if (constructors == null) {
         constructors = new EObjectContainmentEList<DbcConstructor>(DbcConstructor.class, this, DbcmodelPackage.ABSTRACT_DBC_CLASS__CONSTRUCTORS);
      }
      return constructors;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<DbcInterface> getImplements() {
      if (implements_ == null) {
         implements_ = new EObjectResolvingEList<DbcInterface>(DbcInterface.class, this, DbcmodelPackage.ABSTRACT_DBC_CLASS__IMPLEMENTS);
      }
      return implements_;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<String> getImplementsFullNames() {
      if (implementsFullNames == null) {
         implementsFullNames = new EDataTypeUniqueEList<String>(String.class, this, DbcmodelPackage.ABSTRACT_DBC_CLASS__IMPLEMENTS_FULL_NAMES);
      }
      return implementsFullNames;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated NOT
    */
   public DbcConstructor getConstructor(String signature) {
      DbcConstructor result = null;
      Iterator<DbcConstructor> iter = getConstructors().iterator();
      while (result == null && iter.hasNext()) {
         DbcConstructor next = iter.next();
         if (next.getSignature().equals(signature)) {
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
         case DbcmodelPackage.ABSTRACT_DBC_CLASS__CONSTRUCTORS:
            return ((InternalEList<?>)getConstructors()).basicRemove(otherEnd, msgs);
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
         case DbcmodelPackage.ABSTRACT_DBC_CLASS__CONSTRUCTORS:
            return getConstructors();
         case DbcmodelPackage.ABSTRACT_DBC_CLASS__IMPLEMENTS:
            return getImplements();
         case DbcmodelPackage.ABSTRACT_DBC_CLASS__IMPLEMENTS_FULL_NAMES:
            return getImplementsFullNames();
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
         case DbcmodelPackage.ABSTRACT_DBC_CLASS__CONSTRUCTORS:
            getConstructors().clear();
            getConstructors().addAll((Collection<? extends DbcConstructor>)newValue);
            return;
         case DbcmodelPackage.ABSTRACT_DBC_CLASS__IMPLEMENTS:
            getImplements().clear();
            getImplements().addAll((Collection<? extends DbcInterface>)newValue);
            return;
         case DbcmodelPackage.ABSTRACT_DBC_CLASS__IMPLEMENTS_FULL_NAMES:
            getImplementsFullNames().clear();
            getImplementsFullNames().addAll((Collection<? extends String>)newValue);
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
         case DbcmodelPackage.ABSTRACT_DBC_CLASS__CONSTRUCTORS:
            getConstructors().clear();
            return;
         case DbcmodelPackage.ABSTRACT_DBC_CLASS__IMPLEMENTS:
            getImplements().clear();
            return;
         case DbcmodelPackage.ABSTRACT_DBC_CLASS__IMPLEMENTS_FULL_NAMES:
            getImplementsFullNames().clear();
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
         case DbcmodelPackage.ABSTRACT_DBC_CLASS__CONSTRUCTORS:
            return constructors != null && !constructors.isEmpty();
         case DbcmodelPackage.ABSTRACT_DBC_CLASS__IMPLEMENTS:
            return implements_ != null && !implements_.isEmpty();
         case DbcmodelPackage.ABSTRACT_DBC_CLASS__IMPLEMENTS_FULL_NAMES:
            return implementsFullNames != null && !implementsFullNames.isEmpty();
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
      result.append(" (implementsFullNames: ");
      result.append(implementsFullNames);
      result.append(')');
      return result.toString();
   }

} //AbstractDbcClassImpl