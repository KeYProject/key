/**
 */
package org.key_project.stubby.model.dependencymodel.impl;

import java.lang.reflect.InvocationTargetException;
import java.util.Collection;
import java.util.Iterator;

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
import org.key_project.stubby.model.dependencymodel.Field;
import org.key_project.stubby.model.dependencymodel.Method;
import org.key_project.stubby.model.dependencymodel.Type;
import org.key_project.stubby.model.dependencymodel.TypeKind;
import org.key_project.stubby.model.dependencymodel.TypeUsage;
import org.key_project.stubby.model.dependencymodel.TypeVariable;
import org.key_project.stubby.model.dependencymodel.Visibility;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Type</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.TypeImpl#getTypeVariables <em>Type Variables</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.TypeImpl#getMethods <em>Methods</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.TypeImpl#getFields <em>Fields</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.TypeImpl#getKind <em>Kind</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.TypeImpl#getVisibility <em>Visibility</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.TypeImpl#isFinal <em>Final</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.TypeImpl#isStatic <em>Static</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.TypeImpl#getInnerTypes <em>Inner Types</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.TypeImpl#isAbstract <em>Abstract</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.TypeImpl#getPackage <em>Package</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.TypeImpl#getName <em>Name</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.TypeImpl#isSource <em>Source</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.TypeImpl#getImplements <em>Implements</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.TypeImpl#getExtends <em>Extends</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.impl.TypeImpl#getSimpleName <em>Simple Name</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class TypeImpl extends MinimalEObjectImpl.Container implements Type {
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
    * The cached value of the '{@link #getMethods() <em>Methods</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getMethods()
    * @generated
    * @ordered
    */
   protected EList<Method> methods;

   /**
    * The cached value of the '{@link #getFields() <em>Fields</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getFields()
    * @generated
    * @ordered
    */
   protected EList<Field> fields;

   /**
    * The default value of the '{@link #getKind() <em>Kind</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getKind()
    * @generated
    * @ordered
    */
   protected static final TypeKind KIND_EDEFAULT = TypeKind.CLASS;

   /**
    * The cached value of the '{@link #getKind() <em>Kind</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getKind()
    * @generated
    * @ordered
    */
   protected TypeKind kind = KIND_EDEFAULT;

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
    * The cached value of the '{@link #getInnerTypes() <em>Inner Types</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getInnerTypes()
    * @generated
    * @ordered
    */
   protected EList<Type> innerTypes;

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
    * The default value of the '{@link #getPackage() <em>Package</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getPackage()
    * @generated
    * @ordered
    */
   protected static final String PACKAGE_EDEFAULT = null;

   /**
    * The cached value of the '{@link #getPackage() <em>Package</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getPackage()
    * @generated
    * @ordered
    */
   protected String package_ = PACKAGE_EDEFAULT;

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
    * The default value of the '{@link #isSource() <em>Source</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #isSource()
    * @generated
    * @ordered
    */
   protected static final boolean SOURCE_EDEFAULT = false;

   /**
    * The cached value of the '{@link #isSource() <em>Source</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #isSource()
    * @generated
    * @ordered
    */
   protected boolean source = SOURCE_EDEFAULT;

   /**
    * The cached value of the '{@link #getImplements() <em>Implements</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getImplements()
    * @generated
    * @ordered
    */
   protected EList<TypeUsage> implements_;

   /**
    * The cached value of the '{@link #getExtends() <em>Extends</em>}' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getExtends()
    * @generated
    * @ordered
    */
   protected EList<TypeUsage> extends_;

   /**
    * The default value of the '{@link #getSimpleName() <em>Simple Name</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getSimpleName()
    * @generated
    * @ordered
    */
   protected static final String SIMPLE_NAME_EDEFAULT = null;

   /**
    * The cached value of the '{@link #getSimpleName() <em>Simple Name</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #getSimpleName()
    * @generated
    * @ordered
    */
   protected String simpleName = SIMPLE_NAME_EDEFAULT;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected TypeImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EClass eStaticClass() {
      return DependencymodelPackage.Literals.TYPE;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<TypeVariable> getTypeVariables() {
      if (typeVariables == null) {
         typeVariables = new EObjectContainmentEList<TypeVariable>(TypeVariable.class, this, DependencymodelPackage.TYPE__TYPE_VARIABLES);
      }
      return typeVariables;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<Method> getMethods() {
      if (methods == null) {
         methods = new EObjectContainmentEList<Method>(Method.class, this, DependencymodelPackage.TYPE__METHODS);
      }
      return methods;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<Field> getFields() {
      if (fields == null) {
         fields = new EObjectContainmentEList<Field>(Field.class, this, DependencymodelPackage.TYPE__FIELDS);
      }
      return fields;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public TypeKind getKind() {
      return kind;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setKind(TypeKind newKind) {
      TypeKind oldKind = kind;
      kind = newKind == null ? KIND_EDEFAULT : newKind;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.TYPE__KIND, oldKind, kind));
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
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.TYPE__VISIBILITY, oldVisibility, visibility));
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
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.TYPE__FINAL, oldFinal, final_));
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
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.TYPE__STATIC, oldStatic, static_));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<TypeUsage> getExtends() {
      if (extends_ == null) {
         extends_ = new EObjectContainmentEList<TypeUsage>(TypeUsage.class, this, DependencymodelPackage.TYPE__EXTENDS);
      }
      return extends_;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String getSimpleName() {
      return simpleName;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setSimpleName(String newSimpleName) {
      String oldSimpleName = simpleName;
      simpleName = newSimpleName;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.TYPE__SIMPLE_NAME, oldSimpleName, simpleName));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated NOT
    */
   public boolean containsField(final String name) {
      Field field = CollectionUtil.search(getFields(), new IFilter<Field>() {
         @Override
         public boolean select(Field element) {
            return ObjectUtil.equals(element.getName(), name);
         }
      });
      return field != null;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated NOT
    */
   public boolean containsMethod(final String name, final String[] parameters) {
      Method method = CollectionUtil.search(getMethods(), new IFilter<Method>() {
         @Override
         public boolean select(Method element) {
            if (ObjectUtil.equals(element.getName(), name) &&
                element.getParameterTypes().size() == parameters.length) {
               boolean equals = true;
               Iterator<TypeUsage> iter = element.getParameterTypes().iterator();
               int i = 0;
               while (equals && i < parameters.length) {
                  TypeUsage next = iter.next();
                  if (!ObjectUtil.equals(next.getType(), parameters[i])) {
                     equals = false;
                  }
                  i++;
               }
               return equals;
            }
            else {
               return false;
            }
         }
      });
      return method != null;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<TypeUsage> getImplements() {
      if (implements_ == null) {
         implements_ = new EObjectContainmentEList<TypeUsage>(TypeUsage.class, this, DependencymodelPackage.TYPE__IMPLEMENTS);
      }
      return implements_;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EList<Type> getInnerTypes() {
      if (innerTypes == null) {
         innerTypes = new EObjectContainmentEList<Type>(Type.class, this, DependencymodelPackage.TYPE__INNER_TYPES);
      }
      return innerTypes;
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
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.TYPE__ABSTRACT, oldAbstract, abstract_));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String getPackage() {
      return package_;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setPackage(String newPackage) {
      String oldPackage = package_;
      package_ = newPackage;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.TYPE__PACKAGE, oldPackage, package_));
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
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.TYPE__NAME, oldName, name));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public boolean isSource() {
      return source;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void setSource(boolean newSource) {
      boolean oldSource = source;
      source = newSource;
      if (eNotificationRequired())
         eNotify(new ENotificationImpl(this, Notification.SET, DependencymodelPackage.TYPE__SOURCE, oldSource, source));
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public NotificationChain eInverseRemove(InternalEObject otherEnd, int featureID, NotificationChain msgs) {
      switch (featureID) {
         case DependencymodelPackage.TYPE__TYPE_VARIABLES:
            return ((InternalEList<?>)getTypeVariables()).basicRemove(otherEnd, msgs);
         case DependencymodelPackage.TYPE__METHODS:
            return ((InternalEList<?>)getMethods()).basicRemove(otherEnd, msgs);
         case DependencymodelPackage.TYPE__FIELDS:
            return ((InternalEList<?>)getFields()).basicRemove(otherEnd, msgs);
         case DependencymodelPackage.TYPE__INNER_TYPES:
            return ((InternalEList<?>)getInnerTypes()).basicRemove(otherEnd, msgs);
         case DependencymodelPackage.TYPE__IMPLEMENTS:
            return ((InternalEList<?>)getImplements()).basicRemove(otherEnd, msgs);
         case DependencymodelPackage.TYPE__EXTENDS:
            return ((InternalEList<?>)getExtends()).basicRemove(otherEnd, msgs);
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
         case DependencymodelPackage.TYPE__TYPE_VARIABLES:
            return getTypeVariables();
         case DependencymodelPackage.TYPE__METHODS:
            return getMethods();
         case DependencymodelPackage.TYPE__FIELDS:
            return getFields();
         case DependencymodelPackage.TYPE__KIND:
            return getKind();
         case DependencymodelPackage.TYPE__VISIBILITY:
            return getVisibility();
         case DependencymodelPackage.TYPE__FINAL:
            return isFinal();
         case DependencymodelPackage.TYPE__STATIC:
            return isStatic();
         case DependencymodelPackage.TYPE__INNER_TYPES:
            return getInnerTypes();
         case DependencymodelPackage.TYPE__ABSTRACT:
            return isAbstract();
         case DependencymodelPackage.TYPE__PACKAGE:
            return getPackage();
         case DependencymodelPackage.TYPE__NAME:
            return getName();
         case DependencymodelPackage.TYPE__SOURCE:
            return isSource();
         case DependencymodelPackage.TYPE__IMPLEMENTS:
            return getImplements();
         case DependencymodelPackage.TYPE__EXTENDS:
            return getExtends();
         case DependencymodelPackage.TYPE__SIMPLE_NAME:
            return getSimpleName();
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
         case DependencymodelPackage.TYPE__TYPE_VARIABLES:
            getTypeVariables().clear();
            getTypeVariables().addAll((Collection<? extends TypeVariable>)newValue);
            return;
         case DependencymodelPackage.TYPE__METHODS:
            getMethods().clear();
            getMethods().addAll((Collection<? extends Method>)newValue);
            return;
         case DependencymodelPackage.TYPE__FIELDS:
            getFields().clear();
            getFields().addAll((Collection<? extends Field>)newValue);
            return;
         case DependencymodelPackage.TYPE__KIND:
            setKind((TypeKind)newValue);
            return;
         case DependencymodelPackage.TYPE__VISIBILITY:
            setVisibility((Visibility)newValue);
            return;
         case DependencymodelPackage.TYPE__FINAL:
            setFinal((Boolean)newValue);
            return;
         case DependencymodelPackage.TYPE__STATIC:
            setStatic((Boolean)newValue);
            return;
         case DependencymodelPackage.TYPE__INNER_TYPES:
            getInnerTypes().clear();
            getInnerTypes().addAll((Collection<? extends Type>)newValue);
            return;
         case DependencymodelPackage.TYPE__ABSTRACT:
            setAbstract((Boolean)newValue);
            return;
         case DependencymodelPackage.TYPE__PACKAGE:
            setPackage((String)newValue);
            return;
         case DependencymodelPackage.TYPE__NAME:
            setName((String)newValue);
            return;
         case DependencymodelPackage.TYPE__SOURCE:
            setSource((Boolean)newValue);
            return;
         case DependencymodelPackage.TYPE__IMPLEMENTS:
            getImplements().clear();
            getImplements().addAll((Collection<? extends TypeUsage>)newValue);
            return;
         case DependencymodelPackage.TYPE__EXTENDS:
            getExtends().clear();
            getExtends().addAll((Collection<? extends TypeUsage>)newValue);
            return;
         case DependencymodelPackage.TYPE__SIMPLE_NAME:
            setSimpleName((String)newValue);
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
         case DependencymodelPackage.TYPE__TYPE_VARIABLES:
            getTypeVariables().clear();
            return;
         case DependencymodelPackage.TYPE__METHODS:
            getMethods().clear();
            return;
         case DependencymodelPackage.TYPE__FIELDS:
            getFields().clear();
            return;
         case DependencymodelPackage.TYPE__KIND:
            setKind(KIND_EDEFAULT);
            return;
         case DependencymodelPackage.TYPE__VISIBILITY:
            setVisibility(VISIBILITY_EDEFAULT);
            return;
         case DependencymodelPackage.TYPE__FINAL:
            setFinal(FINAL_EDEFAULT);
            return;
         case DependencymodelPackage.TYPE__STATIC:
            setStatic(STATIC_EDEFAULT);
            return;
         case DependencymodelPackage.TYPE__INNER_TYPES:
            getInnerTypes().clear();
            return;
         case DependencymodelPackage.TYPE__ABSTRACT:
            setAbstract(ABSTRACT_EDEFAULT);
            return;
         case DependencymodelPackage.TYPE__PACKAGE:
            setPackage(PACKAGE_EDEFAULT);
            return;
         case DependencymodelPackage.TYPE__NAME:
            setName(NAME_EDEFAULT);
            return;
         case DependencymodelPackage.TYPE__SOURCE:
            setSource(SOURCE_EDEFAULT);
            return;
         case DependencymodelPackage.TYPE__IMPLEMENTS:
            getImplements().clear();
            return;
         case DependencymodelPackage.TYPE__EXTENDS:
            getExtends().clear();
            return;
         case DependencymodelPackage.TYPE__SIMPLE_NAME:
            setSimpleName(SIMPLE_NAME_EDEFAULT);
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
         case DependencymodelPackage.TYPE__TYPE_VARIABLES:
            return typeVariables != null && !typeVariables.isEmpty();
         case DependencymodelPackage.TYPE__METHODS:
            return methods != null && !methods.isEmpty();
         case DependencymodelPackage.TYPE__FIELDS:
            return fields != null && !fields.isEmpty();
         case DependencymodelPackage.TYPE__KIND:
            return kind != KIND_EDEFAULT;
         case DependencymodelPackage.TYPE__VISIBILITY:
            return visibility != VISIBILITY_EDEFAULT;
         case DependencymodelPackage.TYPE__FINAL:
            return final_ != FINAL_EDEFAULT;
         case DependencymodelPackage.TYPE__STATIC:
            return static_ != STATIC_EDEFAULT;
         case DependencymodelPackage.TYPE__INNER_TYPES:
            return innerTypes != null && !innerTypes.isEmpty();
         case DependencymodelPackage.TYPE__ABSTRACT:
            return abstract_ != ABSTRACT_EDEFAULT;
         case DependencymodelPackage.TYPE__PACKAGE:
            return PACKAGE_EDEFAULT == null ? package_ != null : !PACKAGE_EDEFAULT.equals(package_);
         case DependencymodelPackage.TYPE__NAME:
            return NAME_EDEFAULT == null ? name != null : !NAME_EDEFAULT.equals(name);
         case DependencymodelPackage.TYPE__SOURCE:
            return source != SOURCE_EDEFAULT;
         case DependencymodelPackage.TYPE__IMPLEMENTS:
            return implements_ != null && !implements_.isEmpty();
         case DependencymodelPackage.TYPE__EXTENDS:
            return extends_ != null && !extends_.isEmpty();
         case DependencymodelPackage.TYPE__SIMPLE_NAME:
            return SIMPLE_NAME_EDEFAULT == null ? simpleName != null : !SIMPLE_NAME_EDEFAULT.equals(simpleName);
      }
      return super.eIsSet(featureID);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public Object eInvoke(int operationID, EList<?> arguments) throws InvocationTargetException {
      switch (operationID) {
         case DependencymodelPackage.TYPE___CONTAINS_FIELD__STRING:
            return containsField((String)arguments.get(0));
         case DependencymodelPackage.TYPE___CONTAINS_METHOD__STRING_STRING:
            return containsMethod((String)arguments.get(0), (String[])arguments.get(1));
      }
      return super.eInvoke(operationID, arguments);
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
      result.append(" (kind: ");
      result.append(kind);
      result.append(", visibility: ");
      result.append(visibility);
      result.append(", final: ");
      result.append(final_);
      result.append(", static: ");
      result.append(static_);
      result.append(", abstract: ");
      result.append(abstract_);
      result.append(", package: ");
      result.append(package_);
      result.append(", name: ");
      result.append(name);
      result.append(", source: ");
      result.append(source);
      result.append(", simpleName: ");
      result.append(simpleName);
      result.append(')');
      return result.toString();
   }

} //TypeImpl
