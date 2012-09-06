/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package org.key_project.sed.ui.visualization.model.od.impl;

import java.util.Collection;

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.impl.EObjectImpl;

import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.InternalEList;

import org.key_project.sed.ui.visualization.model.od.ODAssociation;
import org.key_project.sed.ui.visualization.model.od.ODObject;
import org.key_project.sed.ui.visualization.model.od.ODPackage;
import org.key_project.sed.ui.visualization.model.od.ODValue;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Object</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.impl.ODObjectImpl#getName <em>Name</em>}</li>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.impl.ODObjectImpl#getType <em>Type</em>}</li>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.impl.ODObjectImpl#getValues <em>Values</em>}</li>
 *   <li>{@link org.key_project.sed.ui.visualization.model.od.impl.ODObjectImpl#getAssociations <em>Associations</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ODObjectImpl extends EObjectImpl implements ODObject {
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
    * The cached value of the '{@link #getValues() <em>Values</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getValues()
    * @generated
    * @ordered
    */
   protected EList<ODValue> values;

   /**
    * The cached value of the '{@link #getAssociations() <em>Associations</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getAssociations()
    * @generated
    * @ordered
    */
   protected EList<ODAssociation> associations;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected ODObjectImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return ODPackage.Literals.OD_OBJECT;
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
         eNotify(new ENotificationImpl(this, Notification.SET, ODPackage.OD_OBJECT__NAME, oldName, name));
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
         eNotify(new ENotificationImpl(this, Notification.SET, ODPackage.OD_OBJECT__TYPE, oldType, type));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<ODValue> getValues() {
      if (values == null) {
         values = new EObjectContainmentEList<ODValue>(ODValue.class, this, ODPackage.OD_OBJECT__VALUES);
      }
      return values;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<ODAssociation> getAssociations() {
      if (associations == null) {
         associations = new EObjectContainmentEList<ODAssociation>(ODAssociation.class, this, ODPackage.OD_OBJECT__ASSOCIATIONS);
      }
      return associations;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public NotificationChain eInverseRemove(InternalEObject otherEnd, int featureID, NotificationChain msgs) {
      switch (featureID) {
         case ODPackage.OD_OBJECT__VALUES:
            return ((InternalEList<?>)getValues()).basicRemove(otherEnd, msgs);
         case ODPackage.OD_OBJECT__ASSOCIATIONS:
            return ((InternalEList<?>)getAssociations()).basicRemove(otherEnd, msgs);
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
         case ODPackage.OD_OBJECT__NAME:
            return getName();
         case ODPackage.OD_OBJECT__TYPE:
            return getType();
         case ODPackage.OD_OBJECT__VALUES:
            return getValues();
         case ODPackage.OD_OBJECT__ASSOCIATIONS:
            return getAssociations();
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
         case ODPackage.OD_OBJECT__NAME:
            setName((String)newValue);
            return;
         case ODPackage.OD_OBJECT__TYPE:
            setType((String)newValue);
            return;
         case ODPackage.OD_OBJECT__VALUES:
            getValues().clear();
            getValues().addAll((Collection<? extends ODValue>)newValue);
            return;
         case ODPackage.OD_OBJECT__ASSOCIATIONS:
            getAssociations().clear();
            getAssociations().addAll((Collection<? extends ODAssociation>)newValue);
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
         case ODPackage.OD_OBJECT__NAME:
            setName(NAME_EDEFAULT);
            return;
         case ODPackage.OD_OBJECT__TYPE:
            setType(TYPE_EDEFAULT);
            return;
         case ODPackage.OD_OBJECT__VALUES:
            getValues().clear();
            return;
         case ODPackage.OD_OBJECT__ASSOCIATIONS:
            getAssociations().clear();
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
         case ODPackage.OD_OBJECT__NAME:
            return NAME_EDEFAULT == null ? name != null : !NAME_EDEFAULT.equals(name);
         case ODPackage.OD_OBJECT__TYPE:
            return TYPE_EDEFAULT == null ? type != null : !TYPE_EDEFAULT.equals(type);
         case ODPackage.OD_OBJECT__VALUES:
            return values != null && !values.isEmpty();
         case ODPackage.OD_OBJECT__ASSOCIATIONS:
            return associations != null && !associations.isEmpty();
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
      result.append(')');
      return result.toString();
   }

} //ODObjectImpl
