/**
 */
package org.key_project.stubby.model.dependencymodel.impl;

import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.impl.MinimalEObjectImpl;

import org.key_project.stubby.model.dependencymodel.AbstractType;
import org.key_project.stubby.model.dependencymodel.DependencymodelPackage;
import org.key_project.stubby.model.dependencymodel.Field;
import org.key_project.stubby.model.dependencymodel.Visibility;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Field</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.FieldImpl#getName <em>Name</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.FieldImpl#getVisibility <em>Visibility</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.FieldImpl#isFinal <em>Final</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.FieldImpl#isStatic <em>Static</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.FieldImpl#getConstantValue <em>Constant Value</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.FieldImpl#getType <em>Type</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class FieldImpl extends MinimalEObjectImpl.Container implements Field {
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
    * The default value of the '{@link #getVisibility() <em>Visibility</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getVisibility()
    * @generated
    * @ordered
    */
   protected static final Visibility VISIBILITY_EDEFAULT = Visibility.PUBLIC;

   /**
    * The cached value of the '{@link #getVisibility() <em>Visibility</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getVisibility()
    * @generated
    * @ordered
    */
   protected Visibility visibility = VISIBILITY_EDEFAULT;

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
    * The default value of the '{@link #getConstantValue() <em>Constant Value</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getConstantValue()
    * @generated
    * @ordered
    */
   protected static final String CONSTANT_VALUE_EDEFAULT = null;

   /**
    * The cached value of the '{@link #getConstantValue() <em>Constant Value</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getConstantValue()
    * @generated
    * @ordered
    */
   protected String constantValue = CONSTANT_VALUE_EDEFAULT;

   /**
    * The cached value of the '{@link #getType() <em>Type</em>}' reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getType()
    * @generated
    * @ordered
    */
   protected AbstractType type;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected FieldImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return DependencymodelPackage.Literals.FIELD;
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
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.FIELD__NAME, oldName, name));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public Visibility getVisibility() {
      return visibility;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setVisibility(Visibility newVisibility) {
      Visibility oldVisibility = visibility;
      visibility = newVisibility == null ? VISIBILITY_EDEFAULT : newVisibility;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.FIELD__VISIBILITY, oldVisibility, visibility));
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
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.FIELD__FINAL, oldFinal, final_));
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
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.FIELD__STATIC, oldStatic, static_));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String getConstantValue() {
      return constantValue;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setConstantValue(String newConstantValue) {
      String oldConstantValue = constantValue;
      constantValue = newConstantValue;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.FIELD__CONSTANT_VALUE, oldConstantValue, constantValue));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public AbstractType getType() {
      if (type != null && type.eIsProxy()) {
         InternalEObject oldType = (InternalEObject)type;
         type = (AbstractType)eResolveProxy(oldType);
         if (type != oldType) {
            if (eNotificationRequired())
               eNotify(new ENotificationImpl(this, Notification.RESOLVE, DependencymodelPackage.FIELD__TYPE, oldType, type));
         }
      }
      return type;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public AbstractType basicGetType() {
      return type;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setType(AbstractType newType) {
      AbstractType oldType = type;
      type = newType;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.FIELD__TYPE, oldType, type));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public Object eGet(int featureID, boolean resolve, boolean coreType) {
      switch (featureID) {
         case DependencymodelPackage.FIELD__NAME:
            return getName();
         case DependencymodelPackage.FIELD__VISIBILITY:
            return getVisibility();
         case DependencymodelPackage.FIELD__FINAL:
            return isFinal();
         case DependencymodelPackage.FIELD__STATIC:
            return isStatic();
         case DependencymodelPackage.FIELD__CONSTANT_VALUE:
            return getConstantValue();
         case DependencymodelPackage.FIELD__TYPE:
            if (resolve) return getType();
            return basicGetType();
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
         case DependencymodelPackage.FIELD__NAME:
            setName((String)newValue);
            return;
         case DependencymodelPackage.FIELD__VISIBILITY:
            setVisibility((Visibility)newValue);
            return;
         case DependencymodelPackage.FIELD__FINAL:
            setFinal((Boolean)newValue);
            return;
         case DependencymodelPackage.FIELD__STATIC:
            setStatic((Boolean)newValue);
            return;
         case DependencymodelPackage.FIELD__CONSTANT_VALUE:
            setConstantValue((String)newValue);
            return;
         case DependencymodelPackage.FIELD__TYPE:
            setType((AbstractType)newValue);
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
         case DependencymodelPackage.FIELD__NAME:
            setName(NAME_EDEFAULT);
            return;
         case DependencymodelPackage.FIELD__VISIBILITY:
            setVisibility(VISIBILITY_EDEFAULT);
            return;
         case DependencymodelPackage.FIELD__FINAL:
            setFinal(FINAL_EDEFAULT);
            return;
         case DependencymodelPackage.FIELD__STATIC:
            setStatic(STATIC_EDEFAULT);
            return;
         case DependencymodelPackage.FIELD__CONSTANT_VALUE:
            setConstantValue(CONSTANT_VALUE_EDEFAULT);
            return;
         case DependencymodelPackage.FIELD__TYPE:
            setType((AbstractType)null);
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
         case DependencymodelPackage.FIELD__NAME:
            return NAME_EDEFAULT == null ? name != null : !NAME_EDEFAULT.equals(name);
         case DependencymodelPackage.FIELD__VISIBILITY:
            return visibility != VISIBILITY_EDEFAULT;
         case DependencymodelPackage.FIELD__FINAL:
            return final_ != FINAL_EDEFAULT;
         case DependencymodelPackage.FIELD__STATIC:
            return static_ != STATIC_EDEFAULT;
         case DependencymodelPackage.FIELD__CONSTANT_VALUE:
            return CONSTANT_VALUE_EDEFAULT == null ? constantValue != null : !CONSTANT_VALUE_EDEFAULT.equals(constantValue);
         case DependencymodelPackage.FIELD__TYPE:
            return type != null;
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
      result.append(", visibility: ");
      result.append(visibility);
      result.append(", final: ");
      result.append(final_);
      result.append(", static: ");
      result.append(static_);
      result.append(", constantValue: ");
      result.append(constantValue);
      result.append(')');
      return result.toString();
   }

} //FieldImpl
