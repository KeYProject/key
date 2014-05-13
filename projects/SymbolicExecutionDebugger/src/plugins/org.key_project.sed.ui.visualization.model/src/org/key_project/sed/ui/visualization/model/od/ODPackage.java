/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

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
    * The meta object id for the '{@link org.key_project.sed.ui.visualization.model.od.impl.AbstractODValueContainerImpl <em>Abstract OD Value Container</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.key_project.sed.ui.visualization.model.od.impl.AbstractODValueContainerImpl
    * @see org.key_project.sed.ui.visualization.model.od.impl.ODPackageImpl#getAbstractODValueContainer()
    * @generated
    */
   int ABSTRACT_OD_VALUE_CONTAINER = 5;

   /**
    * The feature id for the '<em><b>Values</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_OD_VALUE_CONTAINER__VALUES = 0;

   /**
    * The feature id for the '<em><b>Associations</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_OD_VALUE_CONTAINER__ASSOCIATIONS = 1;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_OD_VALUE_CONTAINER__NAME = 2;

   /**
    * The number of structural features of the '<em>Abstract OD Value Container</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_OD_VALUE_CONTAINER_FEATURE_COUNT = 3;

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
    * The feature id for the '<em><b>Values</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_OBJECT__VALUES = ABSTRACT_OD_VALUE_CONTAINER__VALUES;

   /**
    * The feature id for the '<em><b>Associations</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_OBJECT__ASSOCIATIONS = ABSTRACT_OD_VALUE_CONTAINER__ASSOCIATIONS;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_OBJECT__NAME = ABSTRACT_OD_VALUE_CONTAINER__NAME;

   /**
    * The feature id for the '<em><b>Type</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_OBJECT__TYPE = ABSTRACT_OD_VALUE_CONTAINER_FEATURE_COUNT + 0;

   /**
    * The number of structural features of the '<em>Object</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_OBJECT_FEATURE_COUNT = ABSTRACT_OD_VALUE_CONTAINER_FEATURE_COUNT + 1;

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
    * The feature id for the '<em><b>States</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_MODEL__STATES = 1;

   /**
    * The number of structural features of the '<em>Model</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_MODEL_FEATURE_COUNT = 2;

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
    * The meta object id for the '{@link org.key_project.sed.ui.visualization.model.od.impl.ODStateImpl <em>State</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see org.key_project.sed.ui.visualization.model.od.impl.ODStateImpl
    * @see org.key_project.sed.ui.visualization.model.od.impl.ODPackageImpl#getODState()
    * @generated
    */
   int OD_STATE = 4;

   /**
    * The feature id for the '<em><b>Values</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_STATE__VALUES = ABSTRACT_OD_VALUE_CONTAINER__VALUES;

   /**
    * The feature id for the '<em><b>Associations</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_STATE__ASSOCIATIONS = ABSTRACT_OD_VALUE_CONTAINER__ASSOCIATIONS;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_STATE__NAME = ABSTRACT_OD_VALUE_CONTAINER__NAME;

   /**
    * The number of structural features of the '<em>State</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int OD_STATE_FEATURE_COUNT = ABSTRACT_OD_VALUE_CONTAINER_FEATURE_COUNT + 0;


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
    * Returns the meta object for the containment reference list '{@link org.key_project.sed.ui.visualization.model.od.ODModel#getStates <em>States</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>States</em>'.
    * @see org.key_project.sed.ui.visualization.model.od.ODModel#getStates()
    * @see #getODModel()
    * @generated
    */
   EReference getODModel_States();

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
    * Returns the meta object for class '{@link org.key_project.sed.ui.visualization.model.od.ODState <em>State</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>State</em>'.
    * @see org.key_project.sed.ui.visualization.model.od.ODState
    * @generated
    */
   EClass getODState();

   /**
    * Returns the meta object for class '{@link org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer <em>Abstract OD Value Container</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Abstract OD Value Container</em>'.
    * @see org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer
    * @generated
    */
   EClass getAbstractODValueContainer();

   /**
    * Returns the meta object for the containment reference list '{@link org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer#getValues <em>Values</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Values</em>'.
    * @see org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer#getValues()
    * @see #getAbstractODValueContainer()
    * @generated
    */
   EReference getAbstractODValueContainer_Values();

   /**
    * Returns the meta object for the containment reference list '{@link org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer#getAssociations <em>Associations</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Associations</em>'.
    * @see org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer#getAssociations()
    * @see #getAbstractODValueContainer()
    * @generated
    */
   EReference getAbstractODValueContainer_Associations();

   /**
    * Returns the meta object for the attribute '{@link org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer#getName <em>Name</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Name</em>'.
    * @see org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer#getName()
    * @see #getAbstractODValueContainer()
    * @generated
    */
   EAttribute getAbstractODValueContainer_Name();

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
       * The meta object literal for the '<em><b>Type</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute OD_OBJECT__TYPE = eINSTANCE.getODObject_Type();

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
       * The meta object literal for the '<em><b>States</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference OD_MODEL__STATES = eINSTANCE.getODModel_States();

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

      /**
       * The meta object literal for the '{@link org.key_project.sed.ui.visualization.model.od.impl.ODStateImpl <em>State</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see org.key_project.sed.ui.visualization.model.od.impl.ODStateImpl
       * @see org.key_project.sed.ui.visualization.model.od.impl.ODPackageImpl#getODState()
       * @generated
       */
      EClass OD_STATE = eINSTANCE.getODState();

      /**
       * The meta object literal for the '{@link org.key_project.sed.ui.visualization.model.od.impl.AbstractODValueContainerImpl <em>Abstract OD Value Container</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see org.key_project.sed.ui.visualization.model.od.impl.AbstractODValueContainerImpl
       * @see org.key_project.sed.ui.visualization.model.od.impl.ODPackageImpl#getAbstractODValueContainer()
       * @generated
       */
      EClass ABSTRACT_OD_VALUE_CONTAINER = eINSTANCE.getAbstractODValueContainer();

      /**
       * The meta object literal for the '<em><b>Values</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference ABSTRACT_OD_VALUE_CONTAINER__VALUES = eINSTANCE.getAbstractODValueContainer_Values();

      /**
       * The meta object literal for the '<em><b>Associations</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference ABSTRACT_OD_VALUE_CONTAINER__ASSOCIATIONS = eINSTANCE.getAbstractODValueContainer_Associations();

      /**
       * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute ABSTRACT_OD_VALUE_CONTAINER__NAME = eINSTANCE.getAbstractODValueContainer_Name();

   }

} //ODPackage