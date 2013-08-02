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
import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.InternalEList;

import de.hentschel.visualdbc.dbcmodel.AbstractDbcInterface;
import de.hentschel.visualdbc.dbcmodel.DbcAttribute;
import de.hentschel.visualdbc.dbcmodel.DbcMethod;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Abstract Dbc Interface</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcInterfaceImpl#getMethods <em>Methods</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcInterfaceImpl#getAttributes <em>Attributes</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public abstract class AbstractDbcInterfaceImpl extends AbstractDbcTypeImpl implements AbstractDbcInterface {
   /**
    * The cached value of the '{@link #getMethods() <em>Methods</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getMethods()
    * @generated
    * @ordered
    */
   protected EList<DbcMethod> methods;

   /**
    * The cached value of the '{@link #getAttributes() <em>Attributes</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getAttributes()
    * @generated
    * @ordered
    */
   protected EList<DbcAttribute> attributes;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected AbstractDbcInterfaceImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return DbcmodelPackage.Literals.ABSTRACT_DBC_INTERFACE;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<DbcMethod> getMethods() {
      if (methods == null) {
         methods = new EObjectContainmentEList<DbcMethod>(DbcMethod.class, this, DbcmodelPackage.ABSTRACT_DBC_INTERFACE__METHODS);
      }
      return methods;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<DbcAttribute> getAttributes() {
      if (attributes == null) {
         attributes = new EObjectContainmentEList<DbcAttribute>(DbcAttribute.class, this, DbcmodelPackage.ABSTRACT_DBC_INTERFACE__ATTRIBUTES);
      }
      return attributes;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated NOT
    */
   public DbcMethod getMethod(String signature) {
      DbcMethod result = null;
      Iterator<DbcMethod> iter = getMethods().iterator();
      while (result == null && iter.hasNext()) {
         DbcMethod next = iter.next();
         if (next.getSignature().equals(signature)) {
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
   public DbcAttribute getAttribute(String name) {
      DbcAttribute result = null;
      Iterator<DbcAttribute> iter = getAttributes().iterator();
      while (result == null && iter.hasNext()) {
         DbcAttribute next = iter.next();
         if (next.getName().equals(name)) {
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
         case DbcmodelPackage.ABSTRACT_DBC_INTERFACE__METHODS:
            return ((InternalEList<?>)getMethods()).basicRemove(otherEnd, msgs);
         case DbcmodelPackage.ABSTRACT_DBC_INTERFACE__ATTRIBUTES:
            return ((InternalEList<?>)getAttributes()).basicRemove(otherEnd, msgs);
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
         case DbcmodelPackage.ABSTRACT_DBC_INTERFACE__METHODS:
            return getMethods();
         case DbcmodelPackage.ABSTRACT_DBC_INTERFACE__ATTRIBUTES:
            return getAttributes();
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
         case DbcmodelPackage.ABSTRACT_DBC_INTERFACE__METHODS:
            getMethods().clear();
            getMethods().addAll((Collection<? extends DbcMethod>)newValue);
            return;
         case DbcmodelPackage.ABSTRACT_DBC_INTERFACE__ATTRIBUTES:
            getAttributes().clear();
            getAttributes().addAll((Collection<? extends DbcAttribute>)newValue);
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
         case DbcmodelPackage.ABSTRACT_DBC_INTERFACE__METHODS:
            getMethods().clear();
            return;
         case DbcmodelPackage.ABSTRACT_DBC_INTERFACE__ATTRIBUTES:
            getAttributes().clear();
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
         case DbcmodelPackage.ABSTRACT_DBC_INTERFACE__METHODS:
            return methods != null && !methods.isEmpty();
         case DbcmodelPackage.ABSTRACT_DBC_INTERFACE__ATTRIBUTES:
            return attributes != null && !attributes.isEmpty();
      }
      return super.eIsSet(featureID);
   }

} //AbstractDbcInterfaceImpl