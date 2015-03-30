/**
 */
package org.key_project.stubby.model.dependencymodel.impl;

import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

import org.key_project.stubby.model.dependencymodel.AbstractType;
import org.key_project.stubby.model.dependencymodel.ArrayType;
import org.key_project.stubby.model.dependencymodel.DependencymodelPackage;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Array Type</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.ArrayTypeImpl#getBaseType <em>Base Type</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ArrayTypeImpl extends AbstractTypeImpl implements ArrayType {
   /**
    * The cached value of the '{@link #getBaseType() <em>Base Type</em>}' reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getBaseType()
    * @generated
    * @ordered
    */
   protected AbstractType baseType;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected ArrayTypeImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return DependencymodelPackage.Literals.ARRAY_TYPE;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public AbstractType getBaseType() {
      if (baseType != null && baseType.eIsProxy()) {
         InternalEObject oldBaseType = (InternalEObject)baseType;
         baseType = (AbstractType)eResolveProxy(oldBaseType);
         if (baseType != oldBaseType) {
            if (eNotificationRequired())
               eNotify(new ENotificationImpl(this, Notification.RESOLVE, DependencymodelPackage.ARRAY_TYPE__BASE_TYPE, oldBaseType, baseType));
         }
      }
      return baseType;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public AbstractType basicGetBaseType() {
      return baseType;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setBaseType(AbstractType newBaseType) {
      AbstractType oldBaseType = baseType;
      baseType = newBaseType;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.ARRAY_TYPE__BASE_TYPE, oldBaseType, baseType));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public Object eGet(int featureID, boolean resolve, boolean coreType) {
      switch (featureID) {
         case DependencymodelPackage.ARRAY_TYPE__BASE_TYPE:
            if (resolve) return getBaseType();
            return basicGetBaseType();
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
         case DependencymodelPackage.ARRAY_TYPE__BASE_TYPE:
            setBaseType((AbstractType)newValue);
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
         case DependencymodelPackage.ARRAY_TYPE__BASE_TYPE:
            setBaseType((AbstractType)null);
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
         case DependencymodelPackage.ARRAY_TYPE__BASE_TYPE:
            return baseType != null;
      }
      return super.eIsSet(featureID);
   }

} //ArrayTypeImpl
