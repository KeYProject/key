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

import de.hentschel.visualdbc.dbcmodel.DbcInterface;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;

import java.util.Collection;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.util.EDataTypeUniqueEList;
import org.eclipse.emf.ecore.util.EObjectResolvingEList;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Dbc Interface</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcInterfaceImpl#getExtends <em>Extends</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcInterfaceImpl#getExtendsFullNames <em>Extends Full Names</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class DbcInterfaceImpl extends AbstractDbcInterfaceImpl implements DbcInterface {
   /**
    * The cached value of the '{@link #getExtends() <em>Extends</em>}' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getExtends()
    * @generated
    * @ordered
    */
   protected EList<DbcInterface> extends_;

   /**
    * The cached value of the '{@link #getExtendsFullNames() <em>Extends Full Names</em>}' attribute list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getExtendsFullNames()
    * @generated
    * @ordered
    */
   protected EList<String> extendsFullNames;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected DbcInterfaceImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return DbcmodelPackage.Literals.DBC_INTERFACE;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<DbcInterface> getExtends() {
      if (extends_ == null) {
         extends_ = new EObjectResolvingEList<DbcInterface>(DbcInterface.class, this, DbcmodelPackage.DBC_INTERFACE__EXTENDS);
      }
      return extends_;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<String> getExtendsFullNames() {
      if (extendsFullNames == null) {
         extendsFullNames = new EDataTypeUniqueEList<String>(String.class, this, DbcmodelPackage.DBC_INTERFACE__EXTENDS_FULL_NAMES);
      }
      return extendsFullNames;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public Object eGet(int featureID, boolean resolve, boolean coreType) {
      switch (featureID) {
         case DbcmodelPackage.DBC_INTERFACE__EXTENDS:
            return getExtends();
         case DbcmodelPackage.DBC_INTERFACE__EXTENDS_FULL_NAMES:
            return getExtendsFullNames();
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
         case DbcmodelPackage.DBC_INTERFACE__EXTENDS:
            getExtends().clear();
            getExtends().addAll((Collection<? extends DbcInterface>)newValue);
            return;
         case DbcmodelPackage.DBC_INTERFACE__EXTENDS_FULL_NAMES:
            getExtendsFullNames().clear();
            getExtendsFullNames().addAll((Collection<? extends String>)newValue);
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
         case DbcmodelPackage.DBC_INTERFACE__EXTENDS:
            getExtends().clear();
            return;
         case DbcmodelPackage.DBC_INTERFACE__EXTENDS_FULL_NAMES:
            getExtendsFullNames().clear();
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
         case DbcmodelPackage.DBC_INTERFACE__EXTENDS:
            return extends_ != null && !extends_.isEmpty();
         case DbcmodelPackage.DBC_INTERFACE__EXTENDS_FULL_NAMES:
            return extendsFullNames != null && !extendsFullNames.isEmpty();
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
      result.append(" (extendsFullNames: ");
      result.append(extendsFullNames);
      result.append(')');
      return result.toString();
   }

} //DbcInterfaceImpl