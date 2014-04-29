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

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.util.EDataTypeUniqueEList;
import org.eclipse.emf.ecore.util.EObjectResolvingEList;

import de.hentschel.visualdbc.dbcmodel.DbcClass;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Dbc Class</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcClassImpl#isAbstract <em>Abstract</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcClassImpl#isFinal <em>Final</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcClassImpl#getExtends <em>Extends</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcClassImpl#isAnonymous <em>Anonymous</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcClassImpl#getExtendsFullNames <em>Extends Full Names</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class DbcClassImpl extends AbstractDbcClassImpl implements DbcClass {
   /**
    * The default value of the '{@link #isAbstract() <em>Abstract</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #isAbstract()
    * @generated
    * @ordered
    */
   protected static final boolean ABSTRACT_EDEFAULT = false;

   /**
    * The cached value of the '{@link #isAbstract() <em>Abstract</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #isAbstract()
    * @generated
    * @ordered
    */
   protected boolean abstract_ = ABSTRACT_EDEFAULT;

   /**
    * The default value of the '{@link #isFinal() <em>Final</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #isFinal()
    * @generated
    * @ordered
    */
   protected static final boolean FINAL_EDEFAULT = false;

   /**
    * The cached value of the '{@link #isFinal() <em>Final</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #isFinal()
    * @generated
    * @ordered
    */
   protected boolean final_ = FINAL_EDEFAULT;

   /**
    * The cached value of the '{@link #getExtends() <em>Extends</em>}' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getExtends()
    * @generated
    * @ordered
    */
   protected EList<DbcClass> extends_;

   /**
    * The default value of the '{@link #isAnonymous() <em>Anonymous</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #isAnonymous()
    * @generated
    * @ordered
    */
   protected static final boolean ANONYMOUS_EDEFAULT = false;

   /**
    * The cached value of the '{@link #isAnonymous() <em>Anonymous</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #isAnonymous()
    * @generated
    * @ordered
    */
   protected boolean anonymous = ANONYMOUS_EDEFAULT;

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
   protected DbcClassImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return DbcmodelPackage.Literals.DBC_CLASS;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<DbcClass> getExtends() {
      if (extends_ == null) {
         extends_ = new EObjectResolvingEList<DbcClass>(DbcClass.class, this, DbcmodelPackage.DBC_CLASS__EXTENDS);
      }
      return extends_;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public boolean isAnonymous() {
      return anonymous;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setAnonymous(boolean newAnonymous) {
      boolean oldAnonymous = anonymous;
      anonymous = newAnonymous;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DBC_CLASS__ANONYMOUS, oldAnonymous, anonymous));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<String> getExtendsFullNames() {
      if (extendsFullNames == null) {
         extendsFullNames = new EDataTypeUniqueEList<String>(String.class, this, DbcmodelPackage.DBC_CLASS__EXTENDS_FULL_NAMES);
      }
      return extendsFullNames;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public boolean isAbstract() {
      return abstract_;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setAbstract(boolean newAbstract) {
      boolean oldAbstract = abstract_;
      abstract_ = newAbstract;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DBC_CLASS__ABSTRACT, oldAbstract, abstract_));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public boolean isFinal() {
      return final_;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setFinal(boolean newFinal) {
      boolean oldFinal = final_;
      final_ = newFinal;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DBC_CLASS__FINAL, oldFinal, final_));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public Object eGet(int featureID, boolean resolve, boolean coreType) {
      switch (featureID) {
         case DbcmodelPackage.DBC_CLASS__ABSTRACT:
            return isAbstract();
         case DbcmodelPackage.DBC_CLASS__FINAL:
            return isFinal();
         case DbcmodelPackage.DBC_CLASS__EXTENDS:
            return getExtends();
         case DbcmodelPackage.DBC_CLASS__ANONYMOUS:
            return isAnonymous();
         case DbcmodelPackage.DBC_CLASS__EXTENDS_FULL_NAMES:
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
         case DbcmodelPackage.DBC_CLASS__ABSTRACT:
            setAbstract((Boolean)newValue);
            return;
         case DbcmodelPackage.DBC_CLASS__FINAL:
            setFinal((Boolean)newValue);
            return;
         case DbcmodelPackage.DBC_CLASS__EXTENDS:
            getExtends().clear();
            getExtends().addAll((Collection<? extends DbcClass>)newValue);
            return;
         case DbcmodelPackage.DBC_CLASS__ANONYMOUS:
            setAnonymous((Boolean)newValue);
            return;
         case DbcmodelPackage.DBC_CLASS__EXTENDS_FULL_NAMES:
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
         case DbcmodelPackage.DBC_CLASS__ABSTRACT:
            setAbstract(ABSTRACT_EDEFAULT);
            return;
         case DbcmodelPackage.DBC_CLASS__FINAL:
            setFinal(FINAL_EDEFAULT);
            return;
         case DbcmodelPackage.DBC_CLASS__EXTENDS:
            getExtends().clear();
            return;
         case DbcmodelPackage.DBC_CLASS__ANONYMOUS:
            setAnonymous(ANONYMOUS_EDEFAULT);
            return;
         case DbcmodelPackage.DBC_CLASS__EXTENDS_FULL_NAMES:
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
         case DbcmodelPackage.DBC_CLASS__ABSTRACT:
            return abstract_ != ABSTRACT_EDEFAULT;
         case DbcmodelPackage.DBC_CLASS__FINAL:
            return final_ != FINAL_EDEFAULT;
         case DbcmodelPackage.DBC_CLASS__EXTENDS:
            return extends_ != null && !extends_.isEmpty();
         case DbcmodelPackage.DBC_CLASS__ANONYMOUS:
            return anonymous != ANONYMOUS_EDEFAULT;
         case DbcmodelPackage.DBC_CLASS__EXTENDS_FULL_NAMES:
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
      result.append(" (abstract: ");
      result.append(abstract_);
      result.append(", final: ");
      result.append(final_);
      result.append(", anonymous: ");
      result.append(anonymous);
      result.append(", extendsFullNames: ");
      result.append(extendsFullNames);
      result.append(')');
      return result.toString();
   }

} //DbcClassImpl