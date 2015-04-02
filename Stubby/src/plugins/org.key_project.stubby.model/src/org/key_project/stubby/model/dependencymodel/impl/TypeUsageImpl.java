/**
 */
package org.key_project.stubby.model.dependencymodel.impl;

import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.ecore.EClass;

import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.impl.MinimalEObjectImpl;

import org.key_project.stubby.model.dependencymodel.DependencymodelPackage;
import org.key_project.stubby.model.dependencymodel.TypeUsage;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Type Usage</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.TypeUsageImpl#getType <em>Type</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.TypeUsageImpl#getGenericFreeType <em>Generic Free Type</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class TypeUsageImpl extends MinimalEObjectImpl.Container implements TypeUsage {
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
    * The default value of the '{@link #getGenericFreeType() <em>Generic Free Type</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getGenericFreeType()
    * @generated
    * @ordered
    */
   protected static final String GENERIC_FREE_TYPE_EDEFAULT = null;

   /**
    * The cached value of the '{@link #getGenericFreeType() <em>Generic Free Type</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getGenericFreeType()
    * @generated
    * @ordered
    */
   protected String genericFreeType = GENERIC_FREE_TYPE_EDEFAULT;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected TypeUsageImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return DependencymodelPackage.Literals.TYPE_USAGE;
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
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.TYPE_USAGE__TYPE, oldType, type));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String getGenericFreeType() {
      return genericFreeType;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setGenericFreeType(String newGenericFreeType) {
      String oldGenericFreeType = genericFreeType;
      genericFreeType = newGenericFreeType;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.TYPE_USAGE__GENERIC_FREE_TYPE, oldGenericFreeType, genericFreeType));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public Object eGet(int featureID, boolean resolve, boolean coreType) {
      switch (featureID) {
         case DependencymodelPackage.TYPE_USAGE__TYPE:
            return getType();
         case DependencymodelPackage.TYPE_USAGE__GENERIC_FREE_TYPE:
            return getGenericFreeType();
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
         case DependencymodelPackage.TYPE_USAGE__TYPE:
            setType((String)newValue);
            return;
         case DependencymodelPackage.TYPE_USAGE__GENERIC_FREE_TYPE:
            setGenericFreeType((String)newValue);
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
         case DependencymodelPackage.TYPE_USAGE__TYPE:
            setType(TYPE_EDEFAULT);
            return;
         case DependencymodelPackage.TYPE_USAGE__GENERIC_FREE_TYPE:
            setGenericFreeType(GENERIC_FREE_TYPE_EDEFAULT);
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
         case DependencymodelPackage.TYPE_USAGE__TYPE:
            return TYPE_EDEFAULT == null ? type != null : !TYPE_EDEFAULT.equals(type);
         case DependencymodelPackage.TYPE_USAGE__GENERIC_FREE_TYPE:
            return GENERIC_FREE_TYPE_EDEFAULT == null ? genericFreeType != null : !GENERIC_FREE_TYPE_EDEFAULT.equals(genericFreeType);
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
      result.append(" (type: ");
      result.append(type);
      result.append(", genericFreeType: ");
      result.append(genericFreeType);
      result.append(')');
      return result.toString();
   }

} //TypeUsageImpl
