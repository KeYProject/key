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

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.impl.EObjectImpl;
import org.eclipse.emf.ecore.util.EObjectResolvingEList;

import de.hentschel.visualdbc.dbcmodel.DbcAttribute;
import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.DbcVisibility;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Dbc Attribute</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcAttributeImpl#getAllReferences <em>All References</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcAttributeImpl#getName <em>Name</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcAttributeImpl#getType <em>Type</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcAttributeImpl#getVisibility <em>Visibility</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcAttributeImpl#isStatic <em>Static</em>}</li>
 *   <li>{@link de.hentschel.visualdbc.dbcmodel.impl.DbcAttributeImpl#isFinal <em>Final</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class DbcAttributeImpl extends EObjectImpl implements DbcAttribute {
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
    * The default value of the '{@link #getType() <em>Type</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getType()
    * @generated
    * @ordered
    */
   protected static final String TYPE_EDEFAULT = null;

   /**
    * The cached value of the '{@link #getType() <em>Type</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getType()
    * @generated
    * @ordered
    */
   protected String type = TYPE_EDEFAULT;

   /**
    * The default value of the '{@link #getVisibility() <em>Visibility</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getVisibility()
    * @generated
    * @ordered
    */
   protected static final DbcVisibility VISIBILITY_EDEFAULT = DbcVisibility.PRIVATE;

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
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected DbcAttributeImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return DbcmodelPackage.Literals.DBC_ATTRIBUTE;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<DbcProofReference> getAllReferences() {
      if (allReferences == null) {
         allReferences = new EObjectResolvingEList<DbcProofReference>(DbcProofReference.class, this, DbcmodelPackage.DBC_ATTRIBUTE__ALL_REFERENCES);
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
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DBC_ATTRIBUTE__NAME, oldName, name));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String getType() {
      return type;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setType(String newType) {
      String oldType = type;
      type = newType;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DBC_ATTRIBUTE__TYPE, oldType, type));
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
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DBC_ATTRIBUTE__VISIBILITY, oldVisibility, visibility));
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
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DBC_ATTRIBUTE__STATIC, oldStatic, static_));
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
         eNotify(new ENotificationImpl(this, Notification.SET, DbcmodelPackage.DBC_ATTRIBUTE__FINAL, oldFinal, final_));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public Object eGet(int featureID, boolean resolve, boolean coreType) {
      switch (featureID) {
         case DbcmodelPackage.DBC_ATTRIBUTE__ALL_REFERENCES:
            return getAllReferences();
         case DbcmodelPackage.DBC_ATTRIBUTE__NAME:
            return getName();
         case DbcmodelPackage.DBC_ATTRIBUTE__TYPE:
            return getType();
         case DbcmodelPackage.DBC_ATTRIBUTE__VISIBILITY:
            return getVisibility();
         case DbcmodelPackage.DBC_ATTRIBUTE__STATIC:
            return isStatic();
         case DbcmodelPackage.DBC_ATTRIBUTE__FINAL:
            return isFinal();
      }
      return super.eGet(featureID, resolve, coreType);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public void eSet(int featureID, Object newValue) {
      switch (featureID) {
         case DbcmodelPackage.DBC_ATTRIBUTE__NAME:
            setName((String)newValue);
            return;
         case DbcmodelPackage.DBC_ATTRIBUTE__TYPE:
            setType((String)newValue);
            return;
         case DbcmodelPackage.DBC_ATTRIBUTE__VISIBILITY:
            setVisibility((DbcVisibility)newValue);
            return;
         case DbcmodelPackage.DBC_ATTRIBUTE__STATIC:
            setStatic((Boolean)newValue);
            return;
         case DbcmodelPackage.DBC_ATTRIBUTE__FINAL:
            setFinal((Boolean)newValue);
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
         case DbcmodelPackage.DBC_ATTRIBUTE__NAME:
            setName(NAME_EDEFAULT);
            return;
         case DbcmodelPackage.DBC_ATTRIBUTE__TYPE:
            setType(TYPE_EDEFAULT);
            return;
         case DbcmodelPackage.DBC_ATTRIBUTE__VISIBILITY:
            setVisibility(VISIBILITY_EDEFAULT);
            return;
         case DbcmodelPackage.DBC_ATTRIBUTE__STATIC:
            setStatic(STATIC_EDEFAULT);
            return;
         case DbcmodelPackage.DBC_ATTRIBUTE__FINAL:
            setFinal(FINAL_EDEFAULT);
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
         case DbcmodelPackage.DBC_ATTRIBUTE__ALL_REFERENCES:
            return allReferences != null && !allReferences.isEmpty();
         case DbcmodelPackage.DBC_ATTRIBUTE__NAME:
            return NAME_EDEFAULT == null ? name != null : !NAME_EDEFAULT.equals(name);
         case DbcmodelPackage.DBC_ATTRIBUTE__TYPE:
            return TYPE_EDEFAULT == null ? type != null : !TYPE_EDEFAULT.equals(type);
         case DbcmodelPackage.DBC_ATTRIBUTE__VISIBILITY:
            return visibility != VISIBILITY_EDEFAULT;
         case DbcmodelPackage.DBC_ATTRIBUTE__STATIC:
            return static_ != STATIC_EDEFAULT;
         case DbcmodelPackage.DBC_ATTRIBUTE__FINAL:
            return final_ != FINAL_EDEFAULT;
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
      result.append(" (name: ");
      result.append(name);
      result.append(", type: ");
      result.append(type);
      result.append(", visibility: ");
      result.append(visibility);
      result.append(", static: ");
      result.append(static_);
      result.append(", final: ");
      result.append(final_);
      result.append(')');
      return result.toString();
   }

} //DbcAttributeImpl