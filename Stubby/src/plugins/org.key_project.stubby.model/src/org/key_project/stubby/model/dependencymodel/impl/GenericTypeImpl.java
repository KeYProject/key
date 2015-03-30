/**
 */
package org.key_project.stubby.model.dependencymodel.impl;

import java.util.Collection;

import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

import org.eclipse.emf.ecore.util.EObjectResolvingEList;

import org.key_project.stubby.model.dependencymodel.AbstractType;
import org.key_project.stubby.model.dependencymodel.DependencymodelPackage;
import org.key_project.stubby.model.dependencymodel.GenericType;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Generic Type</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.GenericTypeImpl#getBaseType <em>Base Type</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.GenericTypeImpl#getTypeArguments <em>Type Arguments</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class GenericTypeImpl extends AbstractTypeImpl implements GenericType {
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
    * The cached value of the '{@link #getTypeArguments() <em>Type Arguments</em>}' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getTypeArguments()
    * @generated
    * @ordered
    */
   protected EList<AbstractType> typeArguments;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected GenericTypeImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return DependencymodelPackage.Literals.GENERIC_TYPE;
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
               eNotify(new ENotificationImpl(this, Notification.RESOLVE, DependencymodelPackage.GENERIC_TYPE__BASE_TYPE, oldBaseType, baseType));
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
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.GENERIC_TYPE__BASE_TYPE, oldBaseType, baseType));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated NOT
    */
   public EList<AbstractType> getTypeArguments() {
      if (typeArguments == null) {
         typeArguments = new EObjectResolvingEList<AbstractType>(AbstractType.class, this, DependencymodelPackage.GENERIC_TYPE__TYPE_ARGUMENTS) {
            /**
             * Generated UID.
             */
            private static final long serialVersionUID = 2444249960011042301L;

            @Override
            protected boolean isUnique() {
               return false;
            }
         };
      }
      return typeArguments;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public Object eGet(int featureID, boolean resolve, boolean coreType) {
      switch (featureID) {
         case DependencymodelPackage.GENERIC_TYPE__BASE_TYPE:
            if (resolve) return getBaseType();
            return basicGetBaseType();
         case DependencymodelPackage.GENERIC_TYPE__TYPE_ARGUMENTS:
            return getTypeArguments();
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
         case DependencymodelPackage.GENERIC_TYPE__BASE_TYPE:
            setBaseType((AbstractType)newValue);
            return;
         case DependencymodelPackage.GENERIC_TYPE__TYPE_ARGUMENTS:
            getTypeArguments().clear();
            getTypeArguments().addAll((Collection<? extends AbstractType>)newValue);
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
         case DependencymodelPackage.GENERIC_TYPE__BASE_TYPE:
            setBaseType((AbstractType)null);
            return;
         case DependencymodelPackage.GENERIC_TYPE__TYPE_ARGUMENTS:
            getTypeArguments().clear();
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
         case DependencymodelPackage.GENERIC_TYPE__BASE_TYPE:
            return baseType != null;
         case DependencymodelPackage.GENERIC_TYPE__TYPE_ARGUMENTS:
            return typeArguments != null && !typeArguments.isEmpty();
      }
      return super.eIsSet(featureID);
   }

} //GenericTypeImpl
