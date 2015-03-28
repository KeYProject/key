/**
 */
package org.key_project.stubby.model.dependencymodel.impl;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EDataType;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EPackage;

import org.eclipse.emf.ecore.impl.EFactoryImpl;

import org.eclipse.emf.ecore.plugin.EcorePlugin;

import org.key_project.stubby.model.dependencymodel.*;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model <b>Factory</b>.
 * <!-- end-user-doc -->
 * @generated
 */
public class DependencymodelFactoryImpl extends EFactoryImpl implements DependencymodelFactory {
   /**
    * Creates the default factory implementation.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static DependencymodelFactory init() {
      try {
         DependencymodelFactory theDependencymodelFactory = (DependencymodelFactory)EPackage.Registry.INSTANCE.getEFactory(DependencymodelPackage.eNS_URI);
         if (theDependencymodelFactory != null) {
            return theDependencymodelFactory;
         }
      }
      catch (Exception exception) {
         EcorePlugin.INSTANCE.log(exception);
      }
      return new DependencymodelFactoryImpl();
   }

   /**
    * Creates an instance of the factory.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DependencymodelFactoryImpl() {
      super();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public EObject create(EClass eClass) {
      switch (eClass.getClassifierID()) {
         case DependencymodelPackage.TYPE: return createType();
         case DependencymodelPackage.METHOD: return createMethod();
         case DependencymodelPackage.FIELD: return createField();
         case DependencymodelPackage.DEPENDENCY_MODEL: return createDependencyModel();
         case DependencymodelPackage.ARRAY_TYPE: return createArrayType();
         case DependencymodelPackage.DATATYPE: return createDatatype();
         case DependencymodelPackage.GENERIC_TYPE: return createGenericType();
         case DependencymodelPackage.TYPE_VARIABLE: return createTypeVariable();
         case DependencymodelPackage.WILDCARD_TYPE: return createWildcardType();
         default:
            throw new IllegalArgumentException("The class '" + eClass.getName() + "' is not a valid classifier");
      }
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public Object createFromString(EDataType eDataType, String initialValue) {
      switch (eDataType.getClassifierID()) {
         case DependencymodelPackage.TYPE_KIND:
            return createTypeKindFromString(eDataType, initialValue);
         case DependencymodelPackage.VISIBILITY:
            return createVisibilityFromString(eDataType, initialValue);
         default:
            throw new IllegalArgumentException("The datatype '" + eDataType.getName() + "' is not a valid classifier");
      }
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public String convertToString(EDataType eDataType, Object instanceValue) {
      switch (eDataType.getClassifierID()) {
         case DependencymodelPackage.TYPE_KIND:
            return convertTypeKindToString(eDataType, instanceValue);
         case DependencymodelPackage.VISIBILITY:
            return convertVisibilityToString(eDataType, instanceValue);
         default:
            throw new IllegalArgumentException("The datatype '" + eDataType.getName() + "' is not a valid classifier");
      }
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public Type createType() {
      TypeImpl type = new TypeImpl();
      return type;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public Method createMethod() {
      MethodImpl method = new MethodImpl();
      return method;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public Field createField() {
      FieldImpl field = new FieldImpl();
      return field;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DependencyModel createDependencyModel() {
      DependencyModelImpl dependencyModel = new DependencyModelImpl();
      return dependencyModel;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public ArrayType createArrayType() {
      ArrayTypeImpl arrayType = new ArrayTypeImpl();
      return arrayType;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public Datatype createDatatype() {
      DatatypeImpl datatype = new DatatypeImpl();
      return datatype;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public GenericType createGenericType() {
      GenericTypeImpl genericType = new GenericTypeImpl();
      return genericType;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public TypeVariable createTypeVariable() {
      TypeVariableImpl typeVariable = new TypeVariableImpl();
      return typeVariable;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public WildcardType createWildcardType() {
      WildcardTypeImpl wildcardType = new WildcardTypeImpl();
      return wildcardType;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public TypeKind createTypeKindFromString(EDataType eDataType, String initialValue) {
      TypeKind result = TypeKind.get(initialValue);
      if (result == null) throw new IllegalArgumentException("The value '" + initialValue + "' is not a valid enumerator of '" + eDataType.getName() + "'");
      return result;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String convertTypeKindToString(EDataType eDataType, Object instanceValue) {
      return instanceValue == null ? null : instanceValue.toString();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public Visibility createVisibilityFromString(EDataType eDataType, String initialValue) {
      Visibility result = Visibility.get(initialValue);
      if (result == null) throw new IllegalArgumentException("The value '" + initialValue + "' is not a valid enumerator of '" + eDataType.getName() + "'");
      return result;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String convertVisibilityToString(EDataType eDataType, Object instanceValue) {
      return instanceValue == null ? null : instanceValue.toString();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DependencymodelPackage getDependencymodelPackage() {
      return (DependencymodelPackage)getEPackage();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @deprecated
    * @generated
    */
   @Deprecated
   public static DependencymodelPackage getPackage() {
      return DependencymodelPackage.eINSTANCE;
   }

} //DependencymodelFactoryImpl
