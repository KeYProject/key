/**
 */
package org.key_project.stubby.model.dependencymodel.impl;

import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EDataType;
import org.eclipse.emf.ecore.EEnum;
import org.eclipse.emf.ecore.EOperation;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.EReference;

import org.eclipse.emf.ecore.impl.EPackageImpl;

import org.key_project.stubby.model.dependencymodel.DependencyModel;
import org.key_project.stubby.model.dependencymodel.DependencymodelFactory;
import org.key_project.stubby.model.dependencymodel.DependencymodelPackage;
import org.key_project.stubby.model.dependencymodel.Field;
import org.key_project.stubby.model.dependencymodel.ITypeVariableContainer;
import org.key_project.stubby.model.dependencymodel.Method;
import org.key_project.stubby.model.dependencymodel.Type;
import org.key_project.stubby.model.dependencymodel.TypeKind;
import org.key_project.stubby.model.dependencymodel.TypeUsage;
import org.key_project.stubby.model.dependencymodel.TypeVariable;
import org.key_project.stubby.model.dependencymodel.Visibility;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model <b>Package</b>.
 * <!-- end-user-doc -->
 * @generated
 */
public class DependencymodelPackageImpl extends EPackageImpl implements DependencymodelPackage {
   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass typeEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass methodEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass fieldEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass dependencyModelEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass typeVariableEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass iTypeVariableContainerEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass typeUsageEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EEnum typeKindEEnum = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EEnum visibilityEEnum = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EDataType stringArrayEDataType = null;

   /**
    * Creates an instance of the model <b>Package</b>, registered with
    * {@link org.eclipse.emf.ecore.EPackage.Registry EPackage.Registry} by the package
    * package URI value.
    * <p>Note: the correct way to create the package is via the static
    * factory method {@link #init init()}, which also performs
    * initialization of the package, or returns the registered package,
    * if one already exists.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.eclipse.emf.ecore.EPackage.Registry
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#eNS_URI
    * @see #init()
    * @generated
    */
   private DependencymodelPackageImpl() {
      super(eNS_URI, DependencymodelFactory.eINSTANCE);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private static boolean isInited = false;

   /**
    * Creates, registers, and initializes the <b>Package</b> for this model, and for any others upon which it depends.
    * 
    * <p>This method is used to initialize {@link DependencymodelPackage#eINSTANCE} when that field is accessed.
    * Clients should not invoke it directly. Instead, they should simply access that field to obtain the package.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #eNS_URI
    * @see #createPackageContents()
    * @see #initializePackageContents()
    * @generated
    */
   public static DependencymodelPackage init() {
      if (isInited) return (DependencymodelPackage)EPackage.Registry.INSTANCE.getEPackage(DependencymodelPackage.eNS_URI);

      // Obtain or create and register package
      DependencymodelPackageImpl theDependencymodelPackage = (DependencymodelPackageImpl)(EPackage.Registry.INSTANCE.get(eNS_URI) instanceof DependencymodelPackageImpl ? EPackage.Registry.INSTANCE.get(eNS_URI) : new DependencymodelPackageImpl());

      isInited = true;

      // Create package meta-data objects
      theDependencymodelPackage.createPackageContents();

      // Initialize created meta-data
      theDependencymodelPackage.initializePackageContents();

      // Mark meta-data to indicate it can't be changed
      theDependencymodelPackage.freeze();

  
      // Update the registry and return the package
      EPackage.Registry.INSTANCE.put(DependencymodelPackage.eNS_URI, theDependencymodelPackage);
      return theDependencymodelPackage;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getType() {
      return typeEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getType_Methods() {
      return (EReference)typeEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getType_Fields() {
      return (EReference)typeEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getType_Kind() {
      return (EAttribute)typeEClass.getEStructuralFeatures().get(2);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getType_Visibility() {
      return (EAttribute)typeEClass.getEStructuralFeatures().get(3);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getType_Final() {
      return (EAttribute)typeEClass.getEStructuralFeatures().get(4);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getType_Static() {
      return (EAttribute)typeEClass.getEStructuralFeatures().get(5);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getType_Extends() {
      return (EReference)typeEClass.getEStructuralFeatures().get(12);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getType_SimpleName() {
      return (EAttribute)typeEClass.getEStructuralFeatures().get(13);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EOperation getType__ContainsField__String() {
      return typeEClass.getEOperations().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EOperation getType__ContainsMethod__String_String() {
      return typeEClass.getEOperations().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getType_Implements() {
      return (EReference)typeEClass.getEStructuralFeatures().get(11);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getType_InnerTypes() {
      return (EReference)typeEClass.getEStructuralFeatures().get(6);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getType_Abstract() {
      return (EAttribute)typeEClass.getEStructuralFeatures().get(7);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getType_Package() {
      return (EAttribute)typeEClass.getEStructuralFeatures().get(8);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getType_Name() {
      return (EAttribute)typeEClass.getEStructuralFeatures().get(9);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getType_Source() {
      return (EAttribute)typeEClass.getEStructuralFeatures().get(10);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getMethod() {
      return methodEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getMethod_Name() {
      return (EAttribute)methodEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getMethod_Visibility() {
      return (EAttribute)methodEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getMethod_Static() {
      return (EAttribute)methodEClass.getEStructuralFeatures().get(2);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getMethod_Final() {
      return (EAttribute)methodEClass.getEStructuralFeatures().get(3);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getMethod_Abstract() {
      return (EAttribute)methodEClass.getEStructuralFeatures().get(4);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getMethod_Constructor() {
      return (EAttribute)methodEClass.getEStructuralFeatures().get(5);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getMethod_ReturnType() {
      return (EReference)methodEClass.getEStructuralFeatures().get(6);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getMethod_Throws() {
      return (EReference)methodEClass.getEStructuralFeatures().get(7);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getMethod_ParameterTypes() {
      return (EReference)methodEClass.getEStructuralFeatures().get(8);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getField() {
      return fieldEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getField_Name() {
      return (EAttribute)fieldEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getField_Visibility() {
      return (EAttribute)fieldEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getField_Final() {
      return (EAttribute)fieldEClass.getEStructuralFeatures().get(2);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getField_Static() {
      return (EAttribute)fieldEClass.getEStructuralFeatures().get(3);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getField_ConstantValue() {
      return (EAttribute)fieldEClass.getEStructuralFeatures().get(4);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getField_Type() {
      return (EReference)fieldEClass.getEStructuralFeatures().get(5);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getDependencyModel() {
      return dependencyModelEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getDependencyModel_Types() {
      return (EReference)dependencyModelEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getTypeVariable() {
      return typeVariableEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getTypeVariable_Name() {
      return (EAttribute)typeVariableEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getTypeVariable_Type() {
      return (EReference)typeVariableEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getITypeVariableContainer() {
      return iTypeVariableContainerEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getITypeVariableContainer_TypeVariables() {
      return (EReference)iTypeVariableContainerEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getTypeUsage() {
      return typeUsageEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getTypeUsage_Type() {
      return (EAttribute)typeUsageEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getTypeUsage_GenericFreeType() {
      return (EAttribute)typeUsageEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EEnum getTypeKind() {
      return typeKindEEnum;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EEnum getVisibility() {
      return visibilityEEnum;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EDataType getStringArray() {
      return stringArrayEDataType;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DependencymodelFactory getDependencymodelFactory() {
      return (DependencymodelFactory)getEFactoryInstance();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private boolean isCreated = false;

   /**
    * Creates the meta-model objects for the package.  This method is
    * guarded to have no affect on any invocation but its first.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void createPackageContents() {
      if (isCreated) return;
      isCreated = true;

      // Create classes and their features
      typeEClass = createEClass(TYPE);
      createEReference(typeEClass, TYPE__METHODS);
      createEReference(typeEClass, TYPE__FIELDS);
      createEAttribute(typeEClass, TYPE__KIND);
      createEAttribute(typeEClass, TYPE__VISIBILITY);
      createEAttribute(typeEClass, TYPE__FINAL);
      createEAttribute(typeEClass, TYPE__STATIC);
      createEReference(typeEClass, TYPE__INNER_TYPES);
      createEAttribute(typeEClass, TYPE__ABSTRACT);
      createEAttribute(typeEClass, TYPE__PACKAGE);
      createEAttribute(typeEClass, TYPE__NAME);
      createEAttribute(typeEClass, TYPE__SOURCE);
      createEReference(typeEClass, TYPE__IMPLEMENTS);
      createEReference(typeEClass, TYPE__EXTENDS);
      createEAttribute(typeEClass, TYPE__SIMPLE_NAME);
      createEOperation(typeEClass, TYPE___CONTAINS_FIELD__STRING);
      createEOperation(typeEClass, TYPE___CONTAINS_METHOD__STRING_STRING);

      methodEClass = createEClass(METHOD);
      createEAttribute(methodEClass, METHOD__NAME);
      createEAttribute(methodEClass, METHOD__VISIBILITY);
      createEAttribute(methodEClass, METHOD__STATIC);
      createEAttribute(methodEClass, METHOD__FINAL);
      createEAttribute(methodEClass, METHOD__ABSTRACT);
      createEAttribute(methodEClass, METHOD__CONSTRUCTOR);
      createEReference(methodEClass, METHOD__RETURN_TYPE);
      createEReference(methodEClass, METHOD__THROWS);
      createEReference(methodEClass, METHOD__PARAMETER_TYPES);

      fieldEClass = createEClass(FIELD);
      createEAttribute(fieldEClass, FIELD__NAME);
      createEAttribute(fieldEClass, FIELD__VISIBILITY);
      createEAttribute(fieldEClass, FIELD__FINAL);
      createEAttribute(fieldEClass, FIELD__STATIC);
      createEAttribute(fieldEClass, FIELD__CONSTANT_VALUE);
      createEReference(fieldEClass, FIELD__TYPE);

      dependencyModelEClass = createEClass(DEPENDENCY_MODEL);
      createEReference(dependencyModelEClass, DEPENDENCY_MODEL__TYPES);

      typeVariableEClass = createEClass(TYPE_VARIABLE);
      createEAttribute(typeVariableEClass, TYPE_VARIABLE__NAME);
      createEReference(typeVariableEClass, TYPE_VARIABLE__TYPE);

      iTypeVariableContainerEClass = createEClass(ITYPE_VARIABLE_CONTAINER);
      createEReference(iTypeVariableContainerEClass, ITYPE_VARIABLE_CONTAINER__TYPE_VARIABLES);

      typeUsageEClass = createEClass(TYPE_USAGE);
      createEAttribute(typeUsageEClass, TYPE_USAGE__TYPE);
      createEAttribute(typeUsageEClass, TYPE_USAGE__GENERIC_FREE_TYPE);

      // Create enums
      typeKindEEnum = createEEnum(TYPE_KIND);
      visibilityEEnum = createEEnum(VISIBILITY);

      // Create data types
      stringArrayEDataType = createEDataType(STRING_ARRAY);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private boolean isInitialized = false;

   /**
    * Complete the initialization of the package and its meta-model.  This
    * method is guarded to have no affect on any invocation but its first.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public void initializePackageContents() {
      if (isInitialized) return;
      isInitialized = true;

      // Initialize package
      setName(eNAME);
      setNsPrefix(eNS_PREFIX);
      setNsURI(eNS_URI);

      // Create type parameters

      // Set bounds for type parameters

      // Add supertypes to classes
      typeEClass.getESuperTypes().add(this.getITypeVariableContainer());
      methodEClass.getESuperTypes().add(this.getITypeVariableContainer());

      // Initialize classes, features, and operations; add parameters
      initEClass(typeEClass, Type.class, "Type", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEReference(getType_Methods(), this.getMethod(), null, "methods", null, 0, -1, Type.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getType_Fields(), this.getField(), null, "fields", null, 0, -1, Type.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getType_Kind(), this.getTypeKind(), "kind", null, 0, 1, Type.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getType_Visibility(), this.getVisibility(), "visibility", null, 0, 1, Type.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getType_Final(), ecorePackage.getEBoolean(), "final", null, 0, 1, Type.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getType_Static(), ecorePackage.getEBoolean(), "static", null, 0, 1, Type.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getType_InnerTypes(), this.getType(), null, "innerTypes", null, 0, -1, Type.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getType_Abstract(), ecorePackage.getEBoolean(), "abstract", null, 0, 1, Type.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getType_Package(), ecorePackage.getEString(), "package", null, 0, 1, Type.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getType_Name(), ecorePackage.getEString(), "name", null, 0, 1, Type.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getType_Source(), ecorePackage.getEBoolean(), "source", null, 0, 1, Type.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getType_Implements(), this.getTypeUsage(), null, "implements", null, 0, -1, Type.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getType_Extends(), this.getTypeUsage(), null, "extends", null, 0, -1, Type.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getType_SimpleName(), ecorePackage.getEString(), "simpleName", null, 0, 1, Type.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      EOperation op = initEOperation(getType__ContainsField__String(), ecorePackage.getEBoolean(), "containsField", 0, 1, IS_UNIQUE, IS_ORDERED);
      addEParameter(op, ecorePackage.getEString(), "name", 0, 1, IS_UNIQUE, IS_ORDERED);

      op = initEOperation(getType__ContainsMethod__String_String(), ecorePackage.getEBoolean(), "containsMethod", 0, 1, IS_UNIQUE, IS_ORDERED);
      addEParameter(op, ecorePackage.getEString(), "name", 0, 1, IS_UNIQUE, IS_ORDERED);
      addEParameter(op, this.getStringArray(), "parameters", 0, 1, IS_UNIQUE, IS_ORDERED);

      initEClass(methodEClass, Method.class, "Method", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEAttribute(getMethod_Name(), ecorePackage.getEString(), "name", null, 0, 1, Method.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getMethod_Visibility(), this.getVisibility(), "visibility", null, 0, 1, Method.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getMethod_Static(), ecorePackage.getEBoolean(), "static", null, 0, 1, Method.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getMethod_Final(), ecorePackage.getEBoolean(), "final", null, 0, 1, Method.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getMethod_Abstract(), ecorePackage.getEBoolean(), "abstract", null, 0, 1, Method.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getMethod_Constructor(), ecorePackage.getEBoolean(), "constructor", null, 0, 1, Method.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getMethod_ReturnType(), this.getTypeUsage(), null, "returnType", null, 0, 1, Method.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getMethod_Throws(), this.getTypeUsage(), null, "throws", null, 0, -1, Method.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getMethod_ParameterTypes(), this.getTypeUsage(), null, "parameterTypes", null, 0, -1, Method.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(fieldEClass, Field.class, "Field", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEAttribute(getField_Name(), ecorePackage.getEString(), "name", null, 0, 1, Field.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getField_Visibility(), this.getVisibility(), "visibility", null, 0, 1, Field.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getField_Final(), ecorePackage.getEBoolean(), "final", null, 0, 1, Field.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getField_Static(), ecorePackage.getEBoolean(), "static", null, 0, 1, Field.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getField_ConstantValue(), ecorePackage.getEString(), "constantValue", null, 0, 1, Field.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getField_Type(), this.getTypeUsage(), null, "type", null, 0, 1, Field.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(dependencyModelEClass, DependencyModel.class, "DependencyModel", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEReference(getDependencyModel_Types(), this.getType(), null, "types", null, 0, -1, DependencyModel.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(typeVariableEClass, TypeVariable.class, "TypeVariable", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEAttribute(getTypeVariable_Name(), ecorePackage.getEString(), "name", null, 0, 1, TypeVariable.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getTypeVariable_Type(), this.getTypeUsage(), null, "type", null, 0, 1, TypeVariable.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(iTypeVariableContainerEClass, ITypeVariableContainer.class, "ITypeVariableContainer", IS_ABSTRACT, IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEReference(getITypeVariableContainer_TypeVariables(), this.getTypeVariable(), null, "typeVariables", null, 0, -1, ITypeVariableContainer.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(typeUsageEClass, TypeUsage.class, "TypeUsage", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEAttribute(getTypeUsage_Type(), ecorePackage.getEString(), "type", null, 0, 1, TypeUsage.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getTypeUsage_GenericFreeType(), ecorePackage.getEString(), "genericFreeType", null, 0, 1, TypeUsage.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      // Initialize enums and add enum literals
      initEEnum(typeKindEEnum, TypeKind.class, "TypeKind");
      addEEnumLiteral(typeKindEEnum, TypeKind.CLASS);
      addEEnumLiteral(typeKindEEnum, TypeKind.INTERFACE);
      addEEnumLiteral(typeKindEEnum, TypeKind.ENUM);
      addEEnumLiteral(typeKindEEnum, TypeKind.ANNOTATION);

      initEEnum(visibilityEEnum, Visibility.class, "Visibility");
      addEEnumLiteral(visibilityEEnum, Visibility.PUBLIC);
      addEEnumLiteral(visibilityEEnum, Visibility.PROTECTED);
      addEEnumLiteral(visibilityEEnum, Visibility.DEFAULT);
      addEEnumLiteral(visibilityEEnum, Visibility.PRIVATE);

      // Initialize data types
      initEDataType(stringArrayEDataType, String[].class, "StringArray", IS_SERIALIZABLE, !IS_GENERATED_INSTANCE_CLASS);

      // Create resource
      createResource(eNS_URI);
   }

} //DependencymodelPackageImpl
