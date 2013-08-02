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

import de.hentschel.visualdbc.dbcmodel.AbstractDbCContainer;
import de.hentschel.visualdbc.dbcmodel.DbcPackage;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Abstract Db CContainer</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbCContainerImpl#getPackages <em>Packages</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public abstract class AbstractDbCContainerImpl extends AbstractDbcTypeContainerImpl implements AbstractDbCContainer {
   /**
    * The cached value of the '{@link #getPackages() <em>Packages</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getPackages()
    * @generated
    * @ordered
    */
   protected EList<DbcPackage> packages;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected AbstractDbCContainerImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return DbcmodelPackage.Literals.ABSTRACT_DB_CCONTAINER;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<DbcPackage> getPackages() {
      if (packages == null) {
         packages = new EObjectContainmentEList<DbcPackage>(DbcPackage.class, this, DbcmodelPackage.ABSTRACT_DB_CCONTAINER__PACKAGES);
      }
      return packages;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated NOT
    */
   public DbcPackage getPackage(String name) {
      DbcPackage result = null;
      Iterator<DbcPackage> iter = getPackages().iterator();
      while (result == null && iter.hasNext()) {
         DbcPackage next = iter.next();
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
         case DbcmodelPackage.ABSTRACT_DB_CCONTAINER__PACKAGES:
            return ((InternalEList<?>)getPackages()).basicRemove(otherEnd, msgs);
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
         case DbcmodelPackage.ABSTRACT_DB_CCONTAINER__PACKAGES:
            return getPackages();
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
         case DbcmodelPackage.ABSTRACT_DB_CCONTAINER__PACKAGES:
            getPackages().clear();
            getPackages().addAll((Collection<? extends DbcPackage>)newValue);
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
         case DbcmodelPackage.ABSTRACT_DB_CCONTAINER__PACKAGES:
            getPackages().clear();
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
         case DbcmodelPackage.ABSTRACT_DB_CCONTAINER__PACKAGES:
            return packages != null && !packages.isEmpty();
      }
      return super.eIsSet(featureID);
   }

} //AbstractDbCContainerImpl