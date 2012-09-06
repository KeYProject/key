/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package org.key_project.sed.ui.visualization.model.od;

import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.EReference;

/**
 * <!-- begin-user-doc -->
 * The <b>Package</b> for the model.
 * It contains accessors for the meta objects to represent
 * <ul>
 *   <li>each class,</li>
 *   <li>each feature of each class,</li>
 *   <li>each enum,</li>
 *   <li>and each data type</li>
 * </ul>
 * <!-- end-user-doc -->
 * @see org.key_project.sed.ui.visualization.model.od.ODFactory
 * @model kind="package"
 * @generated
 */
public interface ODPackage extends EPackage {
   /**
    * The package name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   String eNAME = "od";

   /**
    * The package namespace URI.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   String eNS_URI = "http://key-project.org/sed/objectdiagram";

   /**
    * The package namespace name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   String eNS_PREFIX = "od";

   /**
    * The singleton instance of the package.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   ODPackage eINSTANCE = org.key_project.sed.ui.visualization.model.od.impl.ODPackageImpl.init();

   /**
    * The meta object id for the '{@link org.key_project.sed.ui.visualization.model.od.impl.ODObjectImpl <em>Object</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.key_project.sed.ui.visualization.model.od.impl.ODObjectImpl
    * @see org.key_project.sed.ui.visualization.model.od.impl.ODPackageImpl#getODObject()
    * @generated
    */
   int OD_OBJECT = 0;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_OBJECT__NAME = 0;

   /**
    * The feature id for the '<em><b>Type</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_OBJECT__TYPE = 1;

   /**
    * The feature id for the '<em><b>Values</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_OBJECT__VALUES = 2;

   /**
    * The feature id for the '<em><b>Associations</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_OBJECT__ASSOCIATIONS = 3;

   /**
    * The number of structural features of the '<em>Object</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_OBJECT_FEATURE_COUNT = 4;

   /**
    * The meta object id for the '{@link org.key_project.sed.ui.visualization.model.od.impl.ODValueImpl <em>Value</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.key_project.sed.ui.visualization.model.od.impl.ODValueImpl
    * @see org.key_project.sed.ui.visualization.model.od.impl.ODPackageImpl#getODValue()
    * @generated
    */
   int OD_VALUE = 1;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_VALUE__NAME = 0;

   /**
    * The feature id for the '<em><b>Type</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_VALUE__TYPE = 1;

   /**
    * The feature id for the '<em><b>Value</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_VALUE__VALUE = 2;

   /**
    * The number of structural features of the '<em>Value</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_VALUE_FEATURE_COUNT = 3;

   /**
    * The meta object id for the '{@link org.key_project.sed.ui.visualization.model.od.impl.ODModelImpl <em>Model</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.key_project.sed.ui.visualization.model.od.impl.ODModelImpl
    * @see org.key_project.sed.ui.visualization.model.od.impl.ODPackageImpl#getODModel()
    * @generated
    */
   int OD_MODEL = 2;

   /**
    * The feature id for the '<em><b>Objects</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_MODEL__OBJECTS = 0;

   /**
    * The number of structural features of the '<em>Model</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_MODEL_FEATURE_COUNT = 1;

   /**
    * The meta object id for the '{@link org.key_project.sed.ui.visualization.model.od.impl.ODAssociationImpl <em>Association</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.key_project.sed.ui.visualization.model.od.impl.ODAssociationImpl
    * @see org.key_project.sed.ui.visualization.model.od.impl.ODPackageImpl#getODAssociation()
    * @generated
    */
   int OD_ASSOCIATION = 3;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_ASSOCIATION__NAME = 0;

   /**
    * The feature id for the '<em><b>Target</b></em>' reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_ASSOCIATION__TARGET = 1;

   /**
    * The number of structural features of the '<em>Association</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_ASSOCIATION_FEATURE_COUNT = 2;


   /**
    * Returns the meta object for class '{@link org.key_project.sed.ui.visualization.model.od.ODObject <em>Object</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Object</em>'.
    * @see org.key_project.sed.ui.visualization.model.od.ODObject
    * @generated
    */
   EClass getODObject();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.sed.ui.visualization.model.od.ODObject#getName <em>Name</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Name</em>'.
    * @see org.key_project.sed.ui.visualization.model.od.ODObject#getName()
    * @see #getODObject()
    * @generated
    */
   EAttribute getODObject_Name();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.sed.ui.visualization.model.od.ODObject#getType <em>Type</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Type</em>'.
    * @see org.key_project.sed.ui.visualization.model.od.ODObject#getType()
    * @see #getODObject()
    * @generated
    */
   EAttribute getODObject_Type();

   /**
    * Returns the meta object for the containment reference list '{@link org.key_project.sed.ui.visualization.model.od.ODObject#getValues <em>Values</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Values</em>'.
    * @see org.key_project.sed.ui.visualization.model.od.ODObject#getValues()
    * @see #getODObject()
    * @generated
    */
   EReference getODObject_Values();

   /**
    * Returns the meta object for the containment reference list '{@link org.key_project.sed.ui.visualization.model.od.ODObject#getAssociations <em>Associations</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Associations</em>'.
    * @see org.key_project.sed.ui.visualization.model.od.ODObject#getAssociations()
    * @see #getODObject()
    * @generated
    */
   EReference getODObject_Associations();

   /**
    * Returns the meta object for class '{@link org.key_project.sed.ui.visualization.model.od.ODValue <em>Value</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Value</em>'.
    * @see org.key_project.sed.ui.visualization.model.od.ODValue
    * @generated
    */
   EClass getODValue();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.sed.ui.visualization.model.od.ODValue#getName <em>Name</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Name</em>'.
    * @see org.key_project.sed.ui.visualization.model.od.ODValue#getName()
    * @see #getODValue()
    * @generated
    */
   EAttribute getODValue_Name();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.sed.ui.visualization.model.od.ODValue#getType <em>Type</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Type</em>'.
    * @see org.key_project.sed.ui.visualization.model.od.ODValue#getType()
    * @see #getODValue()
    * @generated
    */
   EAttribute getODValue_Type();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.sed.ui.visualization.model.od.ODValue#getValue <em>Value</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Value</em>'.
    * @see org.key_project.sed.ui.visualization.model.od.ODValue#getValue()
    * @see #getODValue()
    * @generated
    */
   EAttribute getODValue_Value();

   /**
    * Returns the meta object for class '{@link org.key_project.sed.ui.visualization.model.od.ODModel <em>Model</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Model</em>'.
    * @see org.key_project.sed.ui.visualization.model.od.ODModel
    * @generated
    */
   EClass getODModel();

   /**
    * Returns the meta object for the containment reference list '{@link org.key_project.sed.ui.visualization.model.od.ODModel#getObjects <em>Objects</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Objects</em>'.
    * @see org.key_project.sed.ui.visualization.model.od.ODModel#getObjects()
    * @see #getODModel()
    * @generated
    */
   EReference getODModel_Objects();

   /**
    * Returns the meta object for class '{@link org.key_project.sed.ui.visualization.model.od.ODAssociation <em>Association</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Association</em>'.
    * @see org.key_project.sed.ui.visualization.model.od.ODAssociation
    * @generated
    */
   EClass getODAssociation();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.sed.ui.visualization.model.od.ODAssociation#getName <em>Name</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Name</em>'.
    * @see org.key_project.sed.ui.visualization.model.od.ODAssociation#getName()
    * @see #getODAssociation()
    * @generated
    */
   EAttribute getODAssociation_Name();

   /**
    * Returns the meta object for the reference '{@link org.key_project.sed.ui.visualization.model.od.ODAssociation#getTarget <em>Target</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the reference '<em>Target</em>'.
    * @see org.key_project.sed.ui.visualization.model.od.ODAssociation#getTarget()
    * @see #getODAssociation()
    * @generated
    */
   EReference getODAssociation_Target();

   /**
    * Returns the factory that creates the instances of the model.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the factory that creates the instances of the model.
    * @generated
    */
   ODFactory getODFactory();

   /**
    * <!-- begin-user-doc -->
    * Defines literals for the meta objects that represent
    * <ul>
    *   <li>each class,</li>
    *   <li>each feature of each class,</li>
    *   <li>each enum,</li>
    *   <li>and each data type</li>
    * </ul>
    * <!-- end-user-doc -->
    * @generated
    */
   interface Literals {
      /**
       * The meta object literal for the '{@link org.key_project.sed.ui.visualization.model.od.impl.ODObjectImpl <em>Object</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see org.key_project.sed.ui.visualization.model.od.impl.ODObjectImpl
       * @see org.key_project.sed.ui.visualization.model.od.impl.ODPackageImpl#getODObject()
       * @generated
       */
      EClass OD_OBJECT = eINSTANCE.getODObject();

      /**
       * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute OD_OBJECT__NAME = eINSTANCE.getODObject_Name();

      /**
       * The meta object literal for the '<em><b>Type</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute OD_OBJECT__TYPE = eINSTANCE.getODObject_Type();

      /**
       * The meta object literal for the '<em><b>Values</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference OD_OBJECT__VALUES = eINSTANCE.getODObject_Values();

      /**
       * The meta object literal for the '<em><b>Associations</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference OD_OBJECT__ASSOCIATIONS = eINSTANCE.getODObject_Associations();

      /**
       * The meta object literal for the '{@link org.key_project.sed.ui.visualization.model.od.impl.ODValueImpl <em>Value</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see org.key_project.sed.ui.visualization.model.od.impl.ODValueImpl
       * @see org.key_project.sed.ui.visualization.model.od.impl.ODPackageImpl#getODValue()
       * @generated
       */
      EClass OD_VALUE = eINSTANCE.getODValue();

      /**
       * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute OD_VALUE__NAME = eINSTANCE.getODValue_Name();

      /**
       * The meta object literal for the '<em><b>Type</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute OD_VALUE__TYPE = eINSTANCE.getODValue_Type();

      /**
       * The meta object literal for the '<em><b>Value</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute OD_VALUE__VALUE = eINSTANCE.getODValue_Value();

      /**
       * The meta object literal for the '{@link org.key_project.sed.ui.visualization.model.od.impl.ODModelImpl <em>Model</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see org.key_project.sed.ui.visualization.model.od.impl.ODModelImpl
       * @see org.key_project.sed.ui.visualization.model.od.impl.ODPackageImpl#getODModel()
       * @generated
       */
      EClass OD_MODEL = eINSTANCE.getODModel();

      /**
       * The meta object literal for the '<em><b>Objects</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference OD_MODEL__OBJECTS = eINSTANCE.getODModel_Objects();

      /**
       * The meta object literal for the '{@link org.key_project.sed.ui.visualization.model.od.impl.ODAssociationImpl <em>Association</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see org.key_project.sed.ui.visualization.model.od.impl.ODAssociationImpl
       * @see org.key_project.sed.ui.visualization.model.od.impl.ODPackageImpl#getODAssociation()
       * @generated
       */
      EClass OD_ASSOCIATION = eINSTANCE.getODAssociation();

      /**
       * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute OD_ASSOCIATION__NAME = eINSTANCE.getODAssociation_Name();

      /**
       * The meta object literal for the '<em><b>Target</b></em>' reference feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference OD_ASSOCIATION__TARGET = eINSTANCE.getODAssociation_Target();

   }

} //ODPackage
