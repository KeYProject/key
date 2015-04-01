/**
 */
package org.key_project.stubby.model.dependencymodel.impl;

import java.util.Collection;

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.impl.MinimalEObjectImpl;

import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.InternalEList;

import org.key_project.stubby.model.dependencymodel.DependencymodelPackage;
import org.key_project.stubby.model.dependencymodel.Method;
import org.key_project.stubby.model.dependencymodel.TypeUsage;
import org.key_project.stubby.model.dependencymodel.TypeVariable;
import org.key_project.stubby.model.dependencymodel.Visibility;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Method</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.MethodImpl#getTypeVariables <em>Type Variables</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.MethodImpl#getName <em>Name</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.MethodImpl#getVisibility <em>Visibility</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.MethodImpl#isStatic <em>Static</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.MethodImpl#isFinal <em>Final</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.MethodImpl#isAbstract <em>Abstract</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.MethodImpl#isConstructor <em>Constructor</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.MethodImpl#getReturnType <em>Return Type</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.MethodImpl#getThrows <em>Throws</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.MethodImpl#getParameterTypes <em>Parameter Types</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class MethodImpl extends MinimalEObjectImpl.Container implements Method {
   /**
    * The cached value of the '{@link #getTypeVariables() <em>Type Variables</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getTypeVariables()
    * @generated
    * @ordered
    */
   protected EList<TypeVariable> typeVariables;

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
    * The default value of the '{@link #isConstructor() <em>Constructor</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #isConstructor()
    * @generated
    * @ordered
    */
   protected static final boolean CONSTRUCTOR_EDEFAULT = false;

   /**
    * The cached value of the '{@link #isConstructor() <em>Constructor</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #isConstructor()
    * @generated
    * @ordered
    */
   protected boolean constructor = CONSTRUCTOR_EDEFAULT;

   /**
    * The cached value of the '{@link #getReturnType() <em>Return Type</em>}' containment reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getReturnType()
    * @generated
    * @ordered
    */
   protected TypeUsage returnType;

   /**
    * The cached value of the '{@link #getThrows() <em>Throws</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getThrows()
    * @generated
    * @ordered
    */
   protected EList<TypeUsage> throws_;

   /**
    * The cached value of the '{@link #getParameterTypes() <em>Parameter Types</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getParameterTypes()
    * @generated
    * @ordered
    */
   protected EList<TypeUsage> parameterTypes;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected MethodImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return DependencymodelPackage.Literals.METHOD;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<TypeVariable> getTypeVariables() {
      if (typeVariables == null) {
         typeVariables = new EObjectContainmentEList<TypeVariable>(TypeVariable.class, this, DependencymodelPackage.METHOD__TYPE_VARIABLES);
      }
      return typeVariables;
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
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.METHOD__NAME, oldName, name));
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
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.METHOD__VISIBILITY, oldVisibility, visibility));
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
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.METHOD__STATIC, oldStatic, static_));
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
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.METHOD__FINAL, oldFinal, final_));
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
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.METHOD__ABSTRACT, oldAbstract, abstract_));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public boolean isConstructor() {
      return constructor;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setConstructor(boolean newConstructor) {
      boolean oldConstructor = constructor;
      constructor = newConstructor;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.METHOD__CONSTRUCTOR, oldConstructor, constructor));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public TypeUsage getReturnType() {
      return returnType;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public NotificationChain basicSetReturnType(TypeUsage newReturnType, NotificationChain msgs) {
      TypeUsage oldReturnType = returnType;
      returnType = newReturnType;
      if (eNotificationRequired()) {
         ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DependencymodelPackage.METHOD__RETURN_TYPE, oldReturnType, newReturnType);
         if (msgs == null) msgs = notification; else msgs.add(notification);
      }
      return msgs;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setReturnType(TypeUsage newReturnType) {
      if (newReturnType != returnType) {
         NotificationChain msgs = null;
         if (returnType != null)
            msgs = ((InternalEObject)returnType).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DependencymodelPackage.METHOD__RETURN_TYPE, null, msgs);
         if (newReturnType != null)
            msgs = ((InternalEObject)newReturnType).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DependencymodelPackage.METHOD__RETURN_TYPE, null, msgs);
         msgs = basicSetReturnType(newReturnType, msgs);
         if (msgs != null) msgs.dispatch();
      }
      else if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.METHOD__RETURN_TYPE, newReturnType, newReturnType));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<TypeUsage> getThrows() {
      if (throws_ == null) {
         throws_ = new EObjectContainmentEList<TypeUsage>(TypeUsage.class, this, DependencymodelPackage.METHOD__THROWS);
      }
      return throws_;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<TypeUsage> getParameterTypes() {
      if (parameterTypes == null) {
         parameterTypes = new EObjectContainmentEList<TypeUsage>(TypeUsage.class, this, DependencymodelPackage.METHOD__PARAMETER_TYPES);
      }
      return parameterTypes;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public NotificationChain eInverseRemove(InternalEObject otherEnd, int featureID, NotificationChain msgs) {
      switch (featureID) {
         case DependencymodelPackage.METHOD__TYPE_VARIABLES:
            return ((InternalEList<?>)getTypeVariables()).basicRemove(otherEnd, msgs);
         case DependencymodelPackage.METHOD__RETURN_TYPE:
            return basicSetReturnType(null, msgs);
         case DependencymodelPackage.METHOD__THROWS:
            return ((InternalEList<?>)getThrows()).basicRemove(otherEnd, msgs);
         case DependencymodelPackage.METHOD__PARAMETER_TYPES:
            return ((InternalEList<?>)getParameterTypes()).basicRemove(otherEnd, msgs);
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
         case DependencymodelPackage.METHOD__TYPE_VARIABLES:
            return getTypeVariables();
         case DependencymodelPackage.METHOD__NAME:
            return getName();
         case DependencymodelPackage.METHOD__VISIBILITY:
            return getVisibility();
         case DependencymodelPackage.METHOD__STATIC:
            return isStatic();
         case DependencymodelPackage.METHOD__FINAL:
            return isFinal();
         case DependencymodelPackage.METHOD__ABSTRACT:
            return isAbstract();
         case DependencymodelPackage.METHOD__CONSTRUCTOR:
            return isConstructor();
         case DependencymodelPackage.METHOD__RETURN_TYPE:
            return getReturnType();
         case DependencymodelPackage.METHOD__THROWS:
            return getThrows();
         case DependencymodelPackage.METHOD__PARAMETER_TYPES:
            return getParameterTypes();
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
         case DependencymodelPackage.METHOD__TYPE_VARIABLES:
            getTypeVariables().clear();
            getTypeVariables().addAll((Collection<? extends TypeVariable>)newValue);
            return;
         case DependencymodelPackage.METHOD__NAME:
            setName((String)newValue);
            return;
         case DependencymodelPackage.METHOD__VISIBILITY:
            setVisibility((Visibility)newValue);
            return;
         case DependencymodelPackage.METHOD__STATIC:
            setStatic((Boolean)newValue);
            return;
         case DependencymodelPackage.METHOD__FINAL:
            setFinal((Boolean)newValue);
            return;
         case DependencymodelPackage.METHOD__ABSTRACT:
            setAbstract((Boolean)newValue);
            return;
         case DependencymodelPackage.METHOD__CONSTRUCTOR:
            setConstructor((Boolean)newValue);
            return;
         case DependencymodelPackage.METHOD__RETURN_TYPE:
            setReturnType((TypeUsage)newValue);
            return;
         case DependencymodelPackage.METHOD__THROWS:
            getThrows().clear();
            getThrows().addAll((Collection<? extends TypeUsage>)newValue);
            return;
         case DependencymodelPackage.METHOD__PARAMETER_TYPES:
            getParameterTypes().clear();
            getParameterTypes().addAll((Collection<? extends TypeUsage>)newValue);
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
         case DependencymodelPackage.METHOD__TYPE_VARIABLES:
            getTypeVariables().clear();
            return;
         case DependencymodelPackage.METHOD__NAME:
            setName(NAME_EDEFAULT);
            return;
         case DependencymodelPackage.METHOD__VISIBILITY:
            setVisibility(VISIBILITY_EDEFAULT);
            return;
         case DependencymodelPackage.METHOD__STATIC:
            setStatic(STATIC_EDEFAULT);
            return;
         case DependencymodelPackage.METHOD__FINAL:
            setFinal(FINAL_EDEFAULT);
            return;
         case DependencymodelPackage.METHOD__ABSTRACT:
            setAbstract(ABSTRACT_EDEFAULT);
            return;
         case DependencymodelPackage.METHOD__CONSTRUCTOR:
            setConstructor(CONSTRUCTOR_EDEFAULT);
            return;
         case DependencymodelPackage.METHOD__RETURN_TYPE:
            setReturnType((TypeUsage)null);
            return;
         case DependencymodelPackage.METHOD__THROWS:
            getThrows().clear();
            return;
         case DependencymodelPackage.METHOD__PARAMETER_TYPES:
            getParameterTypes().clear();
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
         case DependencymodelPackage.METHOD__TYPE_VARIABLES:
            return typeVariables != null && !typeVariables.isEmpty();
         case DependencymodelPackage.METHOD__NAME:
            return NAME_EDEFAULT == null ? name != null : !NAME_EDEFAULT.equals(name);
         case DependencymodelPackage.METHOD__VISIBILITY:
            return visibility != VISIBILITY_EDEFAULT;
         case DependencymodelPackage.METHOD__STATIC:
            return static_ != STATIC_EDEFAULT;
         case DependencymodelPackage.METHOD__FINAL:
            return final_ != FINAL_EDEFAULT;
         case DependencymodelPackage.METHOD__ABSTRACT:
            return abstract_ != ABSTRACT_EDEFAULT;
         case DependencymodelPackage.METHOD__CONSTRUCTOR:
            return constructor != CONSTRUCTOR_EDEFAULT;
         case DependencymodelPackage.METHOD__RETURN_TYPE:
            return returnType != null;
         case DependencymodelPackage.METHOD__THROWS:
            return throws_ != null && !throws_.isEmpty();
         case DependencymodelPackage.METHOD__PARAMETER_TYPES:
            return parameterTypes != null && !parameterTypes.isEmpty();
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
      result.append(", static: ");
      result.append(static_);
      result.append(", final: ");
      result.append(final_);
      result.append(", abstract: ");
      result.append(abstract_);
      result.append(", constructor: ");
      result.append(constructor);
      result.append(')');
      return result.toString();
   }

} //MethodImpl
