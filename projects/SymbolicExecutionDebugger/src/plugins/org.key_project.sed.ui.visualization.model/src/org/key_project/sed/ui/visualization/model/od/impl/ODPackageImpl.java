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
package org.key_project.sed.ui.visualization.model.od.impl;

import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.EReference;

import org.eclipse.emf.ecore.impl.EPackageImpl;

import org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer;
import org.key_project.sed.ui.visualization.model.od.ODAssociation;
import org.key_project.sed.ui.visualization.model.od.ODFactory;
import org.key_project.sed.ui.visualization.model.od.ODModel;
import org.key_project.sed.ui.visualization.model.od.ODObject;
import org.key_project.sed.ui.visualization.model.od.ODPackage;
import org.key_project.sed.ui.visualization.model.od.ODState;
import org.key_project.sed.ui.visualization.model.od.ODValue;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model <b>Package</b>.
 * <!-- end-user-doc -->
 * @generated
 */
public class ODPackageImpl extends EPackageImpl implements ODPackage {
   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass odObjectEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass odValueEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass odModelEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass odAssociationEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass odStateEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass abstractODValueContainerEClass = null;

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
    * @see org.key_project.sed.ui.visualization.model.od.ODPackage#eNS_URI
    * @see #init()
    * @generated
    */
   private ODPackageImpl() {
      super(eNS_URI, ODFactory.eINSTANCE);
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
    * <p>This method is used to initialize {@link ODPackage#eINSTANCE} when that field is accessed.
    * Clients should not invoke it directly. Instead, they should simply access that field to obtain the package.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #eNS_URI
    * @see #createPackageContents()
    * @see #initializePackageContents()
    * @generated
    */
   public static ODPackage init() {
      if (isInited) return (ODPackage)EPackage.Registry.INSTANCE.getEPackage(ODPackage.eNS_URI);

      // Obtain or create and register package
      ODPackageImpl theODPackage = (ODPackageImpl)(EPackage.Registry.INSTANCE.get(eNS_URI) instanceof ODPackageImpl ? EPackage.Registry.INSTANCE.get(eNS_URI) : new ODPackageImpl());

      isInited = true;

      // Create package meta-data objects
      theODPackage.createPackageContents();

      // Initialize created meta-data
      theODPackage.initializePackageContents();

      // Mark meta-data to indicate it can't be changed
      theODPackage.freeze();

  
      // Update the registry and return the package
      EPackage.Registry.INSTANCE.put(ODPackage.eNS_URI, theODPackage);
      return theODPackage;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getODObject() {
      return odObjectEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getODObject_Type() {
      return (EAttribute)odObjectEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getODValue() {
      return odValueEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getODValue_Name() {
      return (EAttribute)odValueEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getODValue_Type() {
      return (EAttribute)odValueEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getODValue_Value() {
      return (EAttribute)odValueEClass.getEStructuralFeatures().get(2);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getODModel() {
      return odModelEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getODModel_Objects() {
      return (EReference)odModelEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getODModel_States() {
      return (EReference)odModelEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getODAssociation() {
      return odAssociationEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getODAssociation_Name() {
      return (EAttribute)odAssociationEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getODAssociation_Target() {
      return (EReference)odAssociationEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getODState() {
      return odStateEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getAbstractODValueContainer() {
      return abstractODValueContainerEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getAbstractODValueContainer_Values() {
      return (EReference)abstractODValueContainerEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getAbstractODValueContainer_Associations() {
      return (EReference)abstractODValueContainerEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getAbstractODValueContainer_Name() {
      return (EAttribute)abstractODValueContainerEClass.getEStructuralFeatures().get(2);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public ODFactory getODFactory() {
      return (ODFactory)getEFactoryInstance();
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
      odObjectEClass = createEClass(OD_OBJECT);
      createEAttribute(odObjectEClass, OD_OBJECT__TYPE);

      odValueEClass = createEClass(OD_VALUE);
      createEAttribute(odValueEClass, OD_VALUE__NAME);
      createEAttribute(odValueEClass, OD_VALUE__TYPE);
      createEAttribute(odValueEClass, OD_VALUE__VALUE);

      odModelEClass = createEClass(OD_MODEL);
      createEReference(odModelEClass, OD_MODEL__OBJECTS);
      createEReference(odModelEClass, OD_MODEL__STATES);

      odAssociationEClass = createEClass(OD_ASSOCIATION);
      createEAttribute(odAssociationEClass, OD_ASSOCIATION__NAME);
      createEReference(odAssociationEClass, OD_ASSOCIATION__TARGET);

      odStateEClass = createEClass(OD_STATE);

      abstractODValueContainerEClass = createEClass(ABSTRACT_OD_VALUE_CONTAINER);
      createEReference(abstractODValueContainerEClass, ABSTRACT_OD_VALUE_CONTAINER__VALUES);
      createEReference(abstractODValueContainerEClass, ABSTRACT_OD_VALUE_CONTAINER__ASSOCIATIONS);
      createEAttribute(abstractODValueContainerEClass, ABSTRACT_OD_VALUE_CONTAINER__NAME);
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
      odObjectEClass.getESuperTypes().add(this.getAbstractODValueContainer());
      odStateEClass.getESuperTypes().add(this.getAbstractODValueContainer());

      // Initialize classes and features; add operations and parameters
      initEClass(odObjectEClass, ODObject.class, "ODObject", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEAttribute(getODObject_Type(), ecorePackage.getEString(), "type", null, 0, 1, ODObject.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(odValueEClass, ODValue.class, "ODValue", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEAttribute(getODValue_Name(), ecorePackage.getEString(), "name", null, 0, 1, ODValue.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getODValue_Type(), ecorePackage.getEString(), "type", null, 0, 1, ODValue.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getODValue_Value(), ecorePackage.getEString(), "value", null, 0, 1, ODValue.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(odModelEClass, ODModel.class, "ODModel", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEReference(getODModel_Objects(), this.getODObject(), null, "objects", null, 0, -1, ODModel.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getODModel_States(), this.getODState(), null, "states", null, 0, -1, ODModel.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(odAssociationEClass, ODAssociation.class, "ODAssociation", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEAttribute(getODAssociation_Name(), ecorePackage.getEString(), "name", null, 0, 1, ODAssociation.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getODAssociation_Target(), this.getODObject(), null, "target", null, 1, 1, ODAssociation.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(odStateEClass, ODState.class, "ODState", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

      initEClass(abstractODValueContainerEClass, AbstractODValueContainer.class, "AbstractODValueContainer", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEReference(getAbstractODValueContainer_Values(), this.getODValue(), null, "values", null, 0, -1, AbstractODValueContainer.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getAbstractODValueContainer_Associations(), this.getODAssociation(), null, "associations", null, 0, -1, AbstractODValueContainer.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getAbstractODValueContainer_Name(), ecorePackage.getEString(), "name", null, 0, 1, AbstractODValueContainer.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      // Create resource
      createResource(eNS_URI);
   }

} //ODPackageImpl