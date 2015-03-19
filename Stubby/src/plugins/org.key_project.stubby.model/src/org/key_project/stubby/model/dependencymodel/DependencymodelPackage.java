/**
 */
package org.key_project.stubby.model.dependencymodel;

import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EEnum;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.EReference;

/**
 * <!-- begin-user-doc -->
 * The <b>Package</b> for the model.
 * It contains accessors for the meta objects to represent
 * <ul>
 *   <li>each class,</li>
 *   <li>each feature of each class,</li>
 *   <li>each operation of each class,</li>
 *   <li>each enum,</li>
 *   <li>and each data type</li>
 * </ul>
 * <!-- end-user-doc -->
 * @see org.key_project.stubby.model.dependencymodel.DependencymodelFactory
 * @model kind="package"
 * @generated
 */
public interface DependencymodelPackage extends EPackage {
   /**
    * The package name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   String eNAME = "dependencymodel";

   /**
    * The package namespace URI.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   String eNS_URI = "http://key-project.org/dependencymodel";

   /**
    * The package namespace name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   String eNS_PREFIX = "dependencymodel";

   /**
    * The singleton instance of the package.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   DependencymodelPackage eINSTANCE = org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl.init();

   /**
    * The meta object id for the '{@link org.key_project.stubby.model.dependencymodel.impl.AbstractTypeImpl <em>Abstract Type</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.key_project.stubby.model.dependencymodel.impl.AbstractTypeImpl
    * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getAbstractType()
    * @generated
    */
   int ABSTRACT_TYPE = 4;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_TYPE__NAME = 0;

   /**
    * The feature id for the '<em><b>Source</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_TYPE__SOURCE = 1;

   /**
    * The number of structural features of the '<em>Abstract Type</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_TYPE_FEATURE_COUNT = 2;

   /**
    * The number of operations of the '<em>Abstract Type</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_TYPE_OPERATION_COUNT = 0;

   /**
    * The meta object id for the '{@link org.key_project.stubby.model.dependencymodel.impl.TypeImpl <em>Type</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.key_project.stubby.model.dependencymodel.impl.TypeImpl
    * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getType()
    * @generated
    */
   int TYPE = 0;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE__NAME = ABSTRACT_TYPE__NAME;

   /**
    * The feature id for the '<em><b>Source</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE__SOURCE = ABSTRACT_TYPE__SOURCE;

   /**
    * The feature id for the '<em><b>Type Variables</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE__TYPE_VARIABLES = ABSTRACT_TYPE_FEATURE_COUNT + 0;

   /**
    * The feature id for the '<em><b>Methods</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE__METHODS = ABSTRACT_TYPE_FEATURE_COUNT + 1;

   /**
    * The feature id for the '<em><b>Fields</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE__FIELDS = ABSTRACT_TYPE_FEATURE_COUNT + 2;

   /**
    * The feature id for the '<em><b>Kind</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE__KIND = ABSTRACT_TYPE_FEATURE_COUNT + 3;

   /**
    * The feature id for the '<em><b>Visibility</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE__VISIBILITY = ABSTRACT_TYPE_FEATURE_COUNT + 4;

   /**
    * The feature id for the '<em><b>Final</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE__FINAL = ABSTRACT_TYPE_FEATURE_COUNT + 5;

   /**
    * The feature id for the '<em><b>Static</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE__STATIC = ABSTRACT_TYPE_FEATURE_COUNT + 6;

   /**
    * The feature id for the '<em><b>Extends</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE__EXTENDS = ABSTRACT_TYPE_FEATURE_COUNT + 7;

   /**
    * The feature id for the '<em><b>Implements</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE__IMPLEMENTS = ABSTRACT_TYPE_FEATURE_COUNT + 8;

   /**
    * The feature id for the '<em><b>Inner Types</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE__INNER_TYPES = ABSTRACT_TYPE_FEATURE_COUNT + 9;

   /**
    * The feature id for the '<em><b>Abstract</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE__ABSTRACT = ABSTRACT_TYPE_FEATURE_COUNT + 10;

   /**
    * The feature id for the '<em><b>Package</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE__PACKAGE = ABSTRACT_TYPE_FEATURE_COUNT + 11;

   /**
    * The feature id for the '<em><b>Simple Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE__SIMPLE_NAME = ABSTRACT_TYPE_FEATURE_COUNT + 12;

   /**
    * The number of structural features of the '<em>Type</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE_FEATURE_COUNT = ABSTRACT_TYPE_FEATURE_COUNT + 13;

   /**
    * The number of operations of the '<em>Type</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE_OPERATION_COUNT = ABSTRACT_TYPE_OPERATION_COUNT + 0;

   /**
    * The meta object id for the '{@link org.key_project.stubby.model.dependencymodel.ITypeVariableContainer <em>IType Variable Container</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.key_project.stubby.model.dependencymodel.ITypeVariableContainer
    * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getITypeVariableContainer()
    * @generated
    */
   int ITYPE_VARIABLE_CONTAINER = 10;

   /**
    * The feature id for the '<em><b>Type Variables</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ITYPE_VARIABLE_CONTAINER__TYPE_VARIABLES = 0;

   /**
    * The number of structural features of the '<em>IType Variable Container</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ITYPE_VARIABLE_CONTAINER_FEATURE_COUNT = 1;

   /**
    * The number of operations of the '<em>IType Variable Container</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ITYPE_VARIABLE_CONTAINER_OPERATION_COUNT = 0;

   /**
    * The meta object id for the '{@link org.key_project.stubby.model.dependencymodel.impl.MethodImpl <em>Method</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.key_project.stubby.model.dependencymodel.impl.MethodImpl
    * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getMethod()
    * @generated
    */
   int METHOD = 1;

   /**
    * The feature id for the '<em><b>Type Variables</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int METHOD__TYPE_VARIABLES = ITYPE_VARIABLE_CONTAINER__TYPE_VARIABLES;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int METHOD__NAME = ITYPE_VARIABLE_CONTAINER_FEATURE_COUNT + 0;

   /**
    * The feature id for the '<em><b>Visibility</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int METHOD__VISIBILITY = ITYPE_VARIABLE_CONTAINER_FEATURE_COUNT + 1;

   /**
    * The feature id for the '<em><b>Static</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int METHOD__STATIC = ITYPE_VARIABLE_CONTAINER_FEATURE_COUNT + 2;

   /**
    * The feature id for the '<em><b>Final</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int METHOD__FINAL = ITYPE_VARIABLE_CONTAINER_FEATURE_COUNT + 3;

   /**
    * The feature id for the '<em><b>Abstract</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int METHOD__ABSTRACT = ITYPE_VARIABLE_CONTAINER_FEATURE_COUNT + 4;

   /**
    * The feature id for the '<em><b>Return Type</b></em>' reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int METHOD__RETURN_TYPE = ITYPE_VARIABLE_CONTAINER_FEATURE_COUNT + 5;

   /**
    * The feature id for the '<em><b>Parameter Types</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int METHOD__PARAMETER_TYPES = ITYPE_VARIABLE_CONTAINER_FEATURE_COUNT + 6;

   /**
    * The feature id for the '<em><b>Throws</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int METHOD__THROWS = ITYPE_VARIABLE_CONTAINER_FEATURE_COUNT + 7;

   /**
    * The feature id for the '<em><b>Constructor</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int METHOD__CONSTRUCTOR = ITYPE_VARIABLE_CONTAINER_FEATURE_COUNT + 8;

   /**
    * The number of structural features of the '<em>Method</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int METHOD_FEATURE_COUNT = ITYPE_VARIABLE_CONTAINER_FEATURE_COUNT + 9;

   /**
    * The number of operations of the '<em>Method</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int METHOD_OPERATION_COUNT = ITYPE_VARIABLE_CONTAINER_OPERATION_COUNT + 0;

   /**
    * The meta object id for the '{@link org.key_project.stubby.model.dependencymodel.impl.FieldImpl <em>Field</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.key_project.stubby.model.dependencymodel.impl.FieldImpl
    * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getField()
    * @generated
    */
   int FIELD = 2;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int FIELD__NAME = 0;

   /**
    * The feature id for the '<em><b>Visibility</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int FIELD__VISIBILITY = 1;

   /**
    * The feature id for the '<em><b>Final</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int FIELD__FINAL = 2;

   /**
    * The feature id for the '<em><b>Static</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int FIELD__STATIC = 3;

   /**
    * The feature id for the '<em><b>Constant Value</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int FIELD__CONSTANT_VALUE = 4;

   /**
    * The feature id for the '<em><b>Type</b></em>' reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int FIELD__TYPE = 5;

   /**
    * The number of structural features of the '<em>Field</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int FIELD_FEATURE_COUNT = 6;

   /**
    * The number of operations of the '<em>Field</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int FIELD_OPERATION_COUNT = 0;

   /**
    * The meta object id for the '{@link org.key_project.stubby.model.dependencymodel.impl.DependencyModelImpl <em>Dependency Model</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.key_project.stubby.model.dependencymodel.impl.DependencyModelImpl
    * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getDependencyModel()
    * @generated
    */
   int DEPENDENCY_MODEL = 3;

   /**
    * The feature id for the '<em><b>Types</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DEPENDENCY_MODEL__TYPES = 0;

   /**
    * The number of structural features of the '<em>Dependency Model</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DEPENDENCY_MODEL_FEATURE_COUNT = 1;

   /**
    * The number of operations of the '<em>Dependency Model</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DEPENDENCY_MODEL_OPERATION_COUNT = 0;

   /**
    * The meta object id for the '{@link org.key_project.stubby.model.dependencymodel.impl.ArrayTypeImpl <em>Array Type</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.key_project.stubby.model.dependencymodel.impl.ArrayTypeImpl
    * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getArrayType()
    * @generated
    */
   int ARRAY_TYPE = 5;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ARRAY_TYPE__NAME = ABSTRACT_TYPE__NAME;

   /**
    * The feature id for the '<em><b>Source</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ARRAY_TYPE__SOURCE = ABSTRACT_TYPE__SOURCE;

   /**
    * The feature id for the '<em><b>Base Type</b></em>' reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ARRAY_TYPE__BASE_TYPE = ABSTRACT_TYPE_FEATURE_COUNT + 0;

   /**
    * The number of structural features of the '<em>Array Type</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ARRAY_TYPE_FEATURE_COUNT = ABSTRACT_TYPE_FEATURE_COUNT + 1;

   /**
    * The number of operations of the '<em>Array Type</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ARRAY_TYPE_OPERATION_COUNT = ABSTRACT_TYPE_OPERATION_COUNT + 0;

   /**
    * The meta object id for the '{@link org.key_project.stubby.model.dependencymodel.impl.DatatypeImpl <em>Datatype</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.key_project.stubby.model.dependencymodel.impl.DatatypeImpl
    * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getDatatype()
    * @generated
    */
   int DATATYPE = 6;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DATATYPE__NAME = ABSTRACT_TYPE__NAME;

   /**
    * The feature id for the '<em><b>Source</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DATATYPE__SOURCE = ABSTRACT_TYPE__SOURCE;

   /**
    * The number of structural features of the '<em>Datatype</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DATATYPE_FEATURE_COUNT = ABSTRACT_TYPE_FEATURE_COUNT + 0;

   /**
    * The number of operations of the '<em>Datatype</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DATATYPE_OPERATION_COUNT = ABSTRACT_TYPE_OPERATION_COUNT + 0;

   /**
    * The meta object id for the '{@link org.key_project.stubby.model.dependencymodel.impl.GenericTypeImpl <em>Generic Type</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.key_project.stubby.model.dependencymodel.impl.GenericTypeImpl
    * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getGenericType()
    * @generated
    */
   int GENERIC_TYPE = 7;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int GENERIC_TYPE__NAME = ABSTRACT_TYPE__NAME;

   /**
    * The feature id for the '<em><b>Source</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int GENERIC_TYPE__SOURCE = ABSTRACT_TYPE__SOURCE;

   /**
    * The feature id for the '<em><b>Base Type</b></em>' reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int GENERIC_TYPE__BASE_TYPE = ABSTRACT_TYPE_FEATURE_COUNT + 0;

   /**
    * The feature id for the '<em><b>Type Arguments</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int GENERIC_TYPE__TYPE_ARGUMENTS = ABSTRACT_TYPE_FEATURE_COUNT + 1;

   /**
    * The number of structural features of the '<em>Generic Type</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int GENERIC_TYPE_FEATURE_COUNT = ABSTRACT_TYPE_FEATURE_COUNT + 2;

   /**
    * The number of operations of the '<em>Generic Type</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int GENERIC_TYPE_OPERATION_COUNT = ABSTRACT_TYPE_OPERATION_COUNT + 0;

   /**
    * The meta object id for the '{@link org.key_project.stubby.model.dependencymodel.impl.TypeVariableImpl <em>Type Variable</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.key_project.stubby.model.dependencymodel.impl.TypeVariableImpl
    * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getTypeVariable()
    * @generated
    */
   int TYPE_VARIABLE = 8;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE_VARIABLE__NAME = ABSTRACT_TYPE__NAME;

   /**
    * The feature id for the '<em><b>Source</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE_VARIABLE__SOURCE = ABSTRACT_TYPE__SOURCE;

   /**
    * The feature id for the '<em><b>Type</b></em>' reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE_VARIABLE__TYPE = ABSTRACT_TYPE_FEATURE_COUNT + 0;

   /**
    * The number of structural features of the '<em>Type Variable</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE_VARIABLE_FEATURE_COUNT = ABSTRACT_TYPE_FEATURE_COUNT + 1;

   /**
    * The number of operations of the '<em>Type Variable</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int TYPE_VARIABLE_OPERATION_COUNT = ABSTRACT_TYPE_OPERATION_COUNT + 0;

   /**
    * The meta object id for the '{@link org.key_project.stubby.model.dependencymodel.impl.WildcardTypeImpl <em>Wildcard Type</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.key_project.stubby.model.dependencymodel.impl.WildcardTypeImpl
    * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getWildcardType()
    * @generated
    */
   int WILDCARD_TYPE = 9;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int WILDCARD_TYPE__NAME = ABSTRACT_TYPE__NAME;

   /**
    * The feature id for the '<em><b>Source</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int WILDCARD_TYPE__SOURCE = ABSTRACT_TYPE__SOURCE;

   /**
    * The number of structural features of the '<em>Wildcard Type</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int WILDCARD_TYPE_FEATURE_COUNT = ABSTRACT_TYPE_FEATURE_COUNT + 0;

   /**
    * The number of operations of the '<em>Wildcard Type</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int WILDCARD_TYPE_OPERATION_COUNT = ABSTRACT_TYPE_OPERATION_COUNT + 0;

   /**
    * The meta object id for the '{@link org.key_project.stubby.model.dependencymodel.TypeKind <em>Type Kind</em>}' enum.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.key_project.stubby.model.dependencymodel.TypeKind
    * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getTypeKind()
    * @generated
    */
   int TYPE_KIND = 11;

   /**
    * The meta object id for the '{@link org.key_project.stubby.model.dependencymodel.Visibility <em>Visibility</em>}' enum.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.key_project.stubby.model.dependencymodel.Visibility
    * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getVisibility()
    * @generated
    */
   int VISIBILITY = 12;


   /**
    * Returns the meta object for class '{@link org.key_project.stubby.model.dependencymodel.Type <em>Type</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Type</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Type
    * @generated
    */
   EClass getType();

   /**
    * Returns the meta object for the containment reference list '{@link org.key_project.stubby.model.dependencymodel.Type#getMethods <em>Methods</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Methods</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Type#getMethods()
    * @see #getType()
    * @generated
    */
   EReference getType_Methods();

   /**
    * Returns the meta object for the containment reference list '{@link org.key_project.stubby.model.dependencymodel.Type#getFields <em>Fields</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Fields</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Type#getFields()
    * @see #getType()
    * @generated
    */
   EReference getType_Fields();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.stubby.model.dependencymodel.Type#getKind <em>Kind</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Kind</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Type#getKind()
    * @see #getType()
    * @generated
    */
   EAttribute getType_Kind();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.stubby.model.dependencymodel.Type#getVisibility <em>Visibility</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Visibility</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Type#getVisibility()
    * @see #getType()
    * @generated
    */
   EAttribute getType_Visibility();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.stubby.model.dependencymodel.Type#isFinal <em>Final</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Final</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Type#isFinal()
    * @see #getType()
    * @generated
    */
   EAttribute getType_Final();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.stubby.model.dependencymodel.Type#isStatic <em>Static</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Static</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Type#isStatic()
    * @see #getType()
    * @generated
    */
   EAttribute getType_Static();

   /**
    * Returns the meta object for the reference list '{@link org.key_project.stubby.model.dependencymodel.Type#getExtends <em>Extends</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the reference list '<em>Extends</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Type#getExtends()
    * @see #getType()
    * @generated
    */
   EReference getType_Extends();

   /**
    * Returns the meta object for the reference list '{@link org.key_project.stubby.model.dependencymodel.Type#getImplements <em>Implements</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the reference list '<em>Implements</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Type#getImplements()
    * @see #getType()
    * @generated
    */
   EReference getType_Implements();

   /**
    * Returns the meta object for the containment reference list '{@link org.key_project.stubby.model.dependencymodel.Type#getInnerTypes <em>Inner Types</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Inner Types</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Type#getInnerTypes()
    * @see #getType()
    * @generated
    */
   EReference getType_InnerTypes();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.stubby.model.dependencymodel.Type#isAbstract <em>Abstract</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Abstract</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Type#isAbstract()
    * @see #getType()
    * @generated
    */
   EAttribute getType_Abstract();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.stubby.model.dependencymodel.Type#getPackage <em>Package</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Package</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Type#getPackage()
    * @see #getType()
    * @generated
    */
   EAttribute getType_Package();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.stubby.model.dependencymodel.Type#getSimpleName <em>Simple Name</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Simple Name</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Type#getSimpleName()
    * @see #getType()
    * @generated
    */
   EAttribute getType_SimpleName();

   /**
    * Returns the meta object for class '{@link org.key_project.stubby.model.dependencymodel.Method <em>Method</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Method</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Method
    * @generated
    */
   EClass getMethod();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.stubby.model.dependencymodel.Method#getName <em>Name</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Name</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Method#getName()
    * @see #getMethod()
    * @generated
    */
   EAttribute getMethod_Name();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.stubby.model.dependencymodel.Method#getVisibility <em>Visibility</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Visibility</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Method#getVisibility()
    * @see #getMethod()
    * @generated
    */
   EAttribute getMethod_Visibility();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.stubby.model.dependencymodel.Method#isStatic <em>Static</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Static</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Method#isStatic()
    * @see #getMethod()
    * @generated
    */
   EAttribute getMethod_Static();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.stubby.model.dependencymodel.Method#isFinal <em>Final</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Final</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Method#isFinal()
    * @see #getMethod()
    * @generated
    */
   EAttribute getMethod_Final();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.stubby.model.dependencymodel.Method#isAbstract <em>Abstract</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Abstract</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Method#isAbstract()
    * @see #getMethod()
    * @generated
    */
   EAttribute getMethod_Abstract();

   /**
    * Returns the meta object for the reference '{@link org.key_project.stubby.model.dependencymodel.Method#getReturnType <em>Return Type</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the reference '<em>Return Type</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Method#getReturnType()
    * @see #getMethod()
    * @generated
    */
   EReference getMethod_ReturnType();

   /**
    * Returns the meta object for the reference list '{@link org.key_project.stubby.model.dependencymodel.Method#getParameterTypes <em>Parameter Types</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the reference list '<em>Parameter Types</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Method#getParameterTypes()
    * @see #getMethod()
    * @generated
    */
   EReference getMethod_ParameterTypes();

   /**
    * Returns the meta object for the reference list '{@link org.key_project.stubby.model.dependencymodel.Method#getThrows <em>Throws</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the reference list '<em>Throws</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Method#getThrows()
    * @see #getMethod()
    * @generated
    */
   EReference getMethod_Throws();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.stubby.model.dependencymodel.Method#isConstructor <em>Constructor</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Constructor</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Method#isConstructor()
    * @see #getMethod()
    * @generated
    */
   EAttribute getMethod_Constructor();

   /**
    * Returns the meta object for class '{@link org.key_project.stubby.model.dependencymodel.Field <em>Field</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Field</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Field
    * @generated
    */
   EClass getField();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.stubby.model.dependencymodel.Field#getName <em>Name</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Name</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Field#getName()
    * @see #getField()
    * @generated
    */
   EAttribute getField_Name();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.stubby.model.dependencymodel.Field#getVisibility <em>Visibility</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Visibility</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Field#getVisibility()
    * @see #getField()
    * @generated
    */
   EAttribute getField_Visibility();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.stubby.model.dependencymodel.Field#isFinal <em>Final</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Final</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Field#isFinal()
    * @see #getField()
    * @generated
    */
   EAttribute getField_Final();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.stubby.model.dependencymodel.Field#isStatic <em>Static</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Static</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Field#isStatic()
    * @see #getField()
    * @generated
    */
   EAttribute getField_Static();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.stubby.model.dependencymodel.Field#getConstantValue <em>Constant Value</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Constant Value</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Field#getConstantValue()
    * @see #getField()
    * @generated
    */
   EAttribute getField_ConstantValue();

   /**
    * Returns the meta object for the reference '{@link org.key_project.stubby.model.dependencymodel.Field#getType <em>Type</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the reference '<em>Type</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Field#getType()
    * @see #getField()
    * @generated
    */
   EReference getField_Type();

   /**
    * Returns the meta object for class '{@link org.key_project.stubby.model.dependencymodel.DependencyModel <em>Dependency Model</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Dependency Model</em>'.
    * @see org.key_project.stubby.model.dependencymodel.DependencyModel
    * @generated
    */
   EClass getDependencyModel();

   /**
    * Returns the meta object for the containment reference list '{@link org.key_project.stubby.model.dependencymodel.DependencyModel#getTypes <em>Types</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Types</em>'.
    * @see org.key_project.stubby.model.dependencymodel.DependencyModel#getTypes()
    * @see #getDependencyModel()
    * @generated
    */
   EReference getDependencyModel_Types();

   /**
    * Returns the meta object for class '{@link org.key_project.stubby.model.dependencymodel.AbstractType <em>Abstract Type</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Abstract Type</em>'.
    * @see org.key_project.stubby.model.dependencymodel.AbstractType
    * @generated
    */
   EClass getAbstractType();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.stubby.model.dependencymodel.AbstractType#getName <em>Name</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Name</em>'.
    * @see org.key_project.stubby.model.dependencymodel.AbstractType#getName()
    * @see #getAbstractType()
    * @generated
    */
   EAttribute getAbstractType_Name();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.stubby.model.dependencymodel.AbstractType#isSource <em>Source</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Source</em>'.
    * @see org.key_project.stubby.model.dependencymodel.AbstractType#isSource()
    * @see #getAbstractType()
    * @generated
    */
   EAttribute getAbstractType_Source();

   /**
    * Returns the meta object for class '{@link org.key_project.stubby.model.dependencymodel.ArrayType <em>Array Type</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Array Type</em>'.
    * @see org.key_project.stubby.model.dependencymodel.ArrayType
    * @generated
    */
   EClass getArrayType();

   /**
    * Returns the meta object for the reference '{@link org.key_project.stubby.model.dependencymodel.ArrayType#getBaseType <em>Base Type</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the reference '<em>Base Type</em>'.
    * @see org.key_project.stubby.model.dependencymodel.ArrayType#getBaseType()
    * @see #getArrayType()
    * @generated
    */
   EReference getArrayType_BaseType();

   /**
    * Returns the meta object for class '{@link org.key_project.stubby.model.dependencymodel.Datatype <em>Datatype</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Datatype</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Datatype
    * @generated
    */
   EClass getDatatype();

   /**
    * Returns the meta object for class '{@link org.key_project.stubby.model.dependencymodel.GenericType <em>Generic Type</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Generic Type</em>'.
    * @see org.key_project.stubby.model.dependencymodel.GenericType
    * @generated
    */
   EClass getGenericType();

   /**
    * Returns the meta object for the reference '{@link org.key_project.stubby.model.dependencymodel.GenericType#getBaseType <em>Base Type</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the reference '<em>Base Type</em>'.
    * @see org.key_project.stubby.model.dependencymodel.GenericType#getBaseType()
    * @see #getGenericType()
    * @generated
    */
   EReference getGenericType_BaseType();

   /**
    * Returns the meta object for the reference list '{@link org.key_project.stubby.model.dependencymodel.GenericType#getTypeArguments <em>Type Arguments</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the reference list '<em>Type Arguments</em>'.
    * @see org.key_project.stubby.model.dependencymodel.GenericType#getTypeArguments()
    * @see #getGenericType()
    * @generated
    */
   EReference getGenericType_TypeArguments();

   /**
    * Returns the meta object for class '{@link org.key_project.stubby.model.dependencymodel.TypeVariable <em>Type Variable</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Type Variable</em>'.
    * @see org.key_project.stubby.model.dependencymodel.TypeVariable
    * @generated
    */
   EClass getTypeVariable();

   /**
    * Returns the meta object for the reference '{@link org.key_project.stubby.model.dependencymodel.TypeVariable#getType <em>Type</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the reference '<em>Type</em>'.
    * @see org.key_project.stubby.model.dependencymodel.TypeVariable#getType()
    * @see #getTypeVariable()
    * @generated
    */
   EReference getTypeVariable_Type();

   /**
    * Returns the meta object for class '{@link org.key_project.stubby.model.dependencymodel.WildcardType <em>Wildcard Type</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Wildcard Type</em>'.
    * @see org.key_project.stubby.model.dependencymodel.WildcardType
    * @generated
    */
   EClass getWildcardType();

   /**
    * Returns the meta object for class '{@link org.key_project.stubby.model.dependencymodel.ITypeVariableContainer <em>IType Variable Container</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>IType Variable Container</em>'.
    * @see org.key_project.stubby.model.dependencymodel.ITypeVariableContainer
    * @generated
    */
   EClass getITypeVariableContainer();

   /**
    * Returns the meta object for the containment reference list '{@link org.key_project.stubby.model.dependencymodel.ITypeVariableContainer#getTypeVariables <em>Type Variables</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Type Variables</em>'.
    * @see org.key_project.stubby.model.dependencymodel.ITypeVariableContainer#getTypeVariables()
    * @see #getITypeVariableContainer()
    * @generated
    */
   EReference getITypeVariableContainer_TypeVariables();

   /**
    * Returns the meta object for enum '{@link org.key_project.stubby.model.dependencymodel.TypeKind <em>Type Kind</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for enum '<em>Type Kind</em>'.
    * @see org.key_project.stubby.model.dependencymodel.TypeKind
    * @generated
    */
   EEnum getTypeKind();

   /**
    * Returns the meta object for enum '{@link org.key_project.stubby.model.dependencymodel.Visibility <em>Visibility</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for enum '<em>Visibility</em>'.
    * @see org.key_project.stubby.model.dependencymodel.Visibility
    * @generated
    */
   EEnum getVisibility();

   /**
    * Returns the factory that creates the instances of the model.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the factory that creates the instances of the model.
    * @generated
    */
   DependencymodelFactory getDependencymodelFactory();

   /**
    * <!-- begin-user-doc -->
    * Defines literals for the meta objects that represent
    * <ul>
    *   <li>each class,</li>
    *   <li>each feature of each class,</li>
    *   <li>each operation of each class,</li>
    *   <li>each enum,</li>
    *   <li>and each data type</li>
    * </ul>
    * <!-- end-user-doc -->
    * @generated
    */
   interface Literals {
      /**
       * The meta object literal for the '{@link org.key_project.stubby.model.dependencymodel.impl.TypeImpl <em>Type</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see org.key_project.stubby.model.dependencymodel.impl.TypeImpl
       * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getType()
       * @generated
       */
      EClass TYPE = eINSTANCE.getType();

      /**
       * The meta object literal for the '<em><b>Methods</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference TYPE__METHODS = eINSTANCE.getType_Methods();

      /**
       * The meta object literal for the '<em><b>Fields</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference TYPE__FIELDS = eINSTANCE.getType_Fields();

      /**
       * The meta object literal for the '<em><b>Kind</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute TYPE__KIND = eINSTANCE.getType_Kind();

      /**
       * The meta object literal for the '<em><b>Visibility</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute TYPE__VISIBILITY = eINSTANCE.getType_Visibility();

      /**
       * The meta object literal for the '<em><b>Final</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute TYPE__FINAL = eINSTANCE.getType_Final();

      /**
       * The meta object literal for the '<em><b>Static</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute TYPE__STATIC = eINSTANCE.getType_Static();

      /**
       * The meta object literal for the '<em><b>Extends</b></em>' reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference TYPE__EXTENDS = eINSTANCE.getType_Extends();

      /**
       * The meta object literal for the '<em><b>Implements</b></em>' reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference TYPE__IMPLEMENTS = eINSTANCE.getType_Implements();

      /**
       * The meta object literal for the '<em><b>Inner Types</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference TYPE__INNER_TYPES = eINSTANCE.getType_InnerTypes();

      /**
       * The meta object literal for the '<em><b>Abstract</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute TYPE__ABSTRACT = eINSTANCE.getType_Abstract();

      /**
       * The meta object literal for the '<em><b>Package</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute TYPE__PACKAGE = eINSTANCE.getType_Package();

      /**
       * The meta object literal for the '<em><b>Simple Name</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute TYPE__SIMPLE_NAME = eINSTANCE.getType_SimpleName();

      /**
       * The meta object literal for the '{@link org.key_project.stubby.model.dependencymodel.impl.MethodImpl <em>Method</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see org.key_project.stubby.model.dependencymodel.impl.MethodImpl
       * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getMethod()
       * @generated
       */
      EClass METHOD = eINSTANCE.getMethod();

      /**
       * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute METHOD__NAME = eINSTANCE.getMethod_Name();

      /**
       * The meta object literal for the '<em><b>Visibility</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute METHOD__VISIBILITY = eINSTANCE.getMethod_Visibility();

      /**
       * The meta object literal for the '<em><b>Static</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute METHOD__STATIC = eINSTANCE.getMethod_Static();

      /**
       * The meta object literal for the '<em><b>Final</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute METHOD__FINAL = eINSTANCE.getMethod_Final();

      /**
       * The meta object literal for the '<em><b>Abstract</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute METHOD__ABSTRACT = eINSTANCE.getMethod_Abstract();

      /**
       * The meta object literal for the '<em><b>Return Type</b></em>' reference feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference METHOD__RETURN_TYPE = eINSTANCE.getMethod_ReturnType();

      /**
       * The meta object literal for the '<em><b>Parameter Types</b></em>' reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference METHOD__PARAMETER_TYPES = eINSTANCE.getMethod_ParameterTypes();

      /**
       * The meta object literal for the '<em><b>Throws</b></em>' reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference METHOD__THROWS = eINSTANCE.getMethod_Throws();

      /**
       * The meta object literal for the '<em><b>Constructor</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute METHOD__CONSTRUCTOR = eINSTANCE.getMethod_Constructor();

      /**
       * The meta object literal for the '{@link org.key_project.stubby.model.dependencymodel.impl.FieldImpl <em>Field</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see org.key_project.stubby.model.dependencymodel.impl.FieldImpl
       * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getField()
       * @generated
       */
      EClass FIELD = eINSTANCE.getField();

      /**
       * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute FIELD__NAME = eINSTANCE.getField_Name();

      /**
       * The meta object literal for the '<em><b>Visibility</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute FIELD__VISIBILITY = eINSTANCE.getField_Visibility();

      /**
       * The meta object literal for the '<em><b>Final</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute FIELD__FINAL = eINSTANCE.getField_Final();

      /**
       * The meta object literal for the '<em><b>Static</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute FIELD__STATIC = eINSTANCE.getField_Static();

      /**
       * The meta object literal for the '<em><b>Constant Value</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute FIELD__CONSTANT_VALUE = eINSTANCE.getField_ConstantValue();

      /**
       * The meta object literal for the '<em><b>Type</b></em>' reference feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference FIELD__TYPE = eINSTANCE.getField_Type();

      /**
       * The meta object literal for the '{@link org.key_project.stubby.model.dependencymodel.impl.DependencyModelImpl <em>Dependency Model</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see org.key_project.stubby.model.dependencymodel.impl.DependencyModelImpl
       * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getDependencyModel()
       * @generated
       */
      EClass DEPENDENCY_MODEL = eINSTANCE.getDependencyModel();

      /**
       * The meta object literal for the '<em><b>Types</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference DEPENDENCY_MODEL__TYPES = eINSTANCE.getDependencyModel_Types();

      /**
       * The meta object literal for the '{@link org.key_project.stubby.model.dependencymodel.impl.AbstractTypeImpl <em>Abstract Type</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see org.key_project.stubby.model.dependencymodel.impl.AbstractTypeImpl
       * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getAbstractType()
       * @generated
       */
      EClass ABSTRACT_TYPE = eINSTANCE.getAbstractType();

      /**
       * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute ABSTRACT_TYPE__NAME = eINSTANCE.getAbstractType_Name();

      /**
       * The meta object literal for the '<em><b>Source</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute ABSTRACT_TYPE__SOURCE = eINSTANCE.getAbstractType_Source();

      /**
       * The meta object literal for the '{@link org.key_project.stubby.model.dependencymodel.impl.ArrayTypeImpl <em>Array Type</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see org.key_project.stubby.model.dependencymodel.impl.ArrayTypeImpl
       * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getArrayType()
       * @generated
       */
      EClass ARRAY_TYPE = eINSTANCE.getArrayType();

      /**
       * The meta object literal for the '<em><b>Base Type</b></em>' reference feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference ARRAY_TYPE__BASE_TYPE = eINSTANCE.getArrayType_BaseType();

      /**
       * The meta object literal for the '{@link org.key_project.stubby.model.dependencymodel.impl.DatatypeImpl <em>Datatype</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see org.key_project.stubby.model.dependencymodel.impl.DatatypeImpl
       * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getDatatype()
       * @generated
       */
      EClass DATATYPE = eINSTANCE.getDatatype();

      /**
       * The meta object literal for the '{@link org.key_project.stubby.model.dependencymodel.impl.GenericTypeImpl <em>Generic Type</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see org.key_project.stubby.model.dependencymodel.impl.GenericTypeImpl
       * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getGenericType()
       * @generated
       */
      EClass GENERIC_TYPE = eINSTANCE.getGenericType();

      /**
       * The meta object literal for the '<em><b>Base Type</b></em>' reference feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference GENERIC_TYPE__BASE_TYPE = eINSTANCE.getGenericType_BaseType();

      /**
       * The meta object literal for the '<em><b>Type Arguments</b></em>' reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference GENERIC_TYPE__TYPE_ARGUMENTS = eINSTANCE.getGenericType_TypeArguments();

      /**
       * The meta object literal for the '{@link org.key_project.stubby.model.dependencymodel.impl.TypeVariableImpl <em>Type Variable</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see org.key_project.stubby.model.dependencymodel.impl.TypeVariableImpl
       * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getTypeVariable()
       * @generated
       */
      EClass TYPE_VARIABLE = eINSTANCE.getTypeVariable();

      /**
       * The meta object literal for the '<em><b>Type</b></em>' reference feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference TYPE_VARIABLE__TYPE = eINSTANCE.getTypeVariable_Type();

      /**
       * The meta object literal for the '{@link org.key_project.stubby.model.dependencymodel.impl.WildcardTypeImpl <em>Wildcard Type</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see org.key_project.stubby.model.dependencymodel.impl.WildcardTypeImpl
       * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getWildcardType()
       * @generated
       */
      EClass WILDCARD_TYPE = eINSTANCE.getWildcardType();

      /**
       * The meta object literal for the '{@link org.key_project.stubby.model.dependencymodel.ITypeVariableContainer <em>IType Variable Container</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see org.key_project.stubby.model.dependencymodel.ITypeVariableContainer
       * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getITypeVariableContainer()
       * @generated
       */
      EClass ITYPE_VARIABLE_CONTAINER = eINSTANCE.getITypeVariableContainer();

      /**
       * The meta object literal for the '<em><b>Type Variables</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference ITYPE_VARIABLE_CONTAINER__TYPE_VARIABLES = eINSTANCE.getITypeVariableContainer_TypeVariables();

      /**
       * The meta object literal for the '{@link org.key_project.stubby.model.dependencymodel.TypeKind <em>Type Kind</em>}' enum.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see org.key_project.stubby.model.dependencymodel.TypeKind
       * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getTypeKind()
       * @generated
       */
      EEnum TYPE_KIND = eINSTANCE.getTypeKind();

      /**
       * The meta object literal for the '{@link org.key_project.stubby.model.dependencymodel.Visibility <em>Visibility</em>}' enum.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see org.key_project.stubby.model.dependencymodel.Visibility
       * @see org.key_project.stubby.model.dependencymodel.impl.DependencymodelPackageImpl#getVisibility()
       * @generated
       */
      EEnum VISIBILITY = eINSTANCE.getVisibility();

   }

} //DependencymodelPackage
