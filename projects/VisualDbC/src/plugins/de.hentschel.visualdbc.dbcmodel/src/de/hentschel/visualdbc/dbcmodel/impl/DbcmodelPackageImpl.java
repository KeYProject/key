/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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
package de.hentschel.visualdbc.dbcmodel.impl;

import java.util.Properties;

import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EDataType;
import org.eclipse.emf.ecore.EEnum;
import org.eclipse.emf.ecore.EOperation;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.EReference;
import org.eclipse.emf.ecore.impl.EPackageImpl;

import de.hentschel.visualdbc.dbcmodel.AbstractDbCContainer;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcClass;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcEnum;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcInterface;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcProofContainer;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcSpecification;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcType;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcTypeContainer;
import de.hentschel.visualdbc.dbcmodel.DbCAxiomContract;
import de.hentschel.visualdbc.dbcmodel.DbcAttribute;
import de.hentschel.visualdbc.dbcmodel.DbcAxiom;
import de.hentschel.visualdbc.dbcmodel.DbcClass;
import de.hentschel.visualdbc.dbcmodel.DbcConstructor;
import de.hentschel.visualdbc.dbcmodel.DbcEnum;
import de.hentschel.visualdbc.dbcmodel.DbcEnumLiteral;
import de.hentschel.visualdbc.dbcmodel.DbcInterface;
import de.hentschel.visualdbc.dbcmodel.DbcInvariant;
import de.hentschel.visualdbc.dbcmodel.DbcMethod;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.DbcOperationContract;
import de.hentschel.visualdbc.dbcmodel.DbcPackage;
import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofObligation;
import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.DbcProofStatus;
import de.hentschel.visualdbc.dbcmodel.DbcProperty;
import de.hentschel.visualdbc.dbcmodel.DbcVisibility;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
import de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable;
import de.hentschel.visualdbc.dbcmodel.IDbCProvable;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model <b>Package</b>.
 * <!-- end-user-doc -->
 * @generated
 */
public class DbcmodelPackageImpl extends EPackageImpl implements DbcmodelPackage {
   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass dbcModelEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass dbcPackageEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass dbcClassEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass abstractDbcProofContainerEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass dbcMethodEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass dbcInvariantEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass dbcProofEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass dbcConstructorEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass dbcProofReferenceEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass dbcAttributeEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass abstractDbcClassEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass abstractDbcInterfaceEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass dbcInterfaceEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass abstractDbcTypeEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass abstractDbcEnumEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass dbcEnumEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass dbcEnumLiteralEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass dbcOperationContractEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass abstractDbcSpecificationEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass dbcPropertyEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass abstractDbcOperationEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass abstractDbCContainerEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass abstractDbcTypeContainerEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass iDbCProvableEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass iDbCProofReferencableEClass = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass dbcProofObligationEClass = null;

   /**
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    */
    private EClass dbcAxiomEClass = null;

/**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EClass dbCAxiomContractEClass = null;

/**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EEnum dbcVisibilityEEnum = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EEnum dbcProofStatusEEnum = null;

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   private EDataType propertiesEDataType = null;

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
    * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage#eNS_URI
    * @see #init()
    * @generated
    */
   private DbcmodelPackageImpl() {
      super(eNS_URI, DbcmodelFactory.eINSTANCE);
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
    * <p>This method is used to initialize {@link DbcmodelPackage#eINSTANCE} when that field is accessed.
    * Clients should not invoke it directly. Instead, they should simply access that field to obtain the package.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see #eNS_URI
    * @see #createPackageContents()
    * @see #initializePackageContents()
    * @generated
    */
   public static DbcmodelPackage init() {
      if (isInited) return (DbcmodelPackage)EPackage.Registry.INSTANCE.getEPackage(DbcmodelPackage.eNS_URI);

      // Obtain or create and register package
      DbcmodelPackageImpl theDbcmodelPackage = (DbcmodelPackageImpl)(EPackage.Registry.INSTANCE.get(eNS_URI) instanceof DbcmodelPackageImpl ? EPackage.Registry.INSTANCE.get(eNS_URI) : new DbcmodelPackageImpl());

      isInited = true;

      // Create package meta-data objects
      theDbcmodelPackage.createPackageContents();

      // Initialize created meta-data
      theDbcmodelPackage.initializePackageContents();

      // Mark meta-data to indicate it can't be changed
      theDbcmodelPackage.freeze();

  
      // Update the registry and return the package
      EPackage.Registry.INSTANCE.put(DbcmodelPackage.eNS_URI, theDbcmodelPackage);
      return theDbcmodelPackage;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getDbcModel() {
      return dbcModelEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcModel_DriverId() {
      return (EAttribute)dbcModelEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getDbcModel_ConnectionSettings() {
      return (EReference)dbcModelEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getDbcModel_ProofObligations() {
      return (EReference)dbcModelEClass.getEStructuralFeatures().get(2);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getDbcPackage() {
      return dbcPackageEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcPackage_Name() {
      return (EAttribute)dbcPackageEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getDbcClass() {
      return dbcClassEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getDbcClass_Extends() {
      return (EReference)dbcClassEClass.getEStructuralFeatures().get(2);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcClass_Anonymous() {
      return (EAttribute)dbcClassEClass.getEStructuralFeatures().get(3);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getAbstractDbcProofContainer() {
      return abstractDbcProofContainerEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getAbstractDbcProofContainer_Proofs() {
      return (EReference)abstractDbcProofContainerEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcClass_Abstract() {
      return (EAttribute)dbcClassEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcClass_Final() {
      return (EAttribute)dbcClassEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getDbcMethod() {
      return dbcMethodEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcMethod_ReturnType() {
      return (EAttribute)dbcMethodEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcMethod_Abstract() {
      return (EAttribute)dbcMethodEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcMethod_Final() {
      return (EAttribute)dbcMethodEClass.getEStructuralFeatures().get(2);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getDbcInvariant() {
      return dbcInvariantEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcInvariant_Condition() {
      return (EAttribute)dbcInvariantEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getDbcProof() {
      return dbcProofEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcProof_Obligation() {
      return (EAttribute)dbcProofEClass.getEStructuralFeatures().get(2);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getDbcProof_Target() {
      return (EReference)dbcProofEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getDbcProof_ProofReferences() {
      return (EReference)dbcProofEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcProof_Status() {
      return (EAttribute)dbcProofEClass.getEStructuralFeatures().get(3);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getDbcConstructor() {
      return dbcConstructorEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getDbcProofReference() {
      return dbcProofReferenceEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getDbcProofReference_Target() {
      return (EReference)dbcProofReferenceEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcProofReference_Kind() {
      return (EAttribute)dbcProofReferenceEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getDbcProofReference_Source() {
      return (EReference)dbcProofReferenceEClass.getEStructuralFeatures().get(2);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getDbcAttribute() {
      return dbcAttributeEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcAttribute_Name() {
      return (EAttribute)dbcAttributeEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcAttribute_Type() {
      return (EAttribute)dbcAttributeEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcAttribute_Visibility() {
      return (EAttribute)dbcAttributeEClass.getEStructuralFeatures().get(2);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcAttribute_Static() {
      return (EAttribute)dbcAttributeEClass.getEStructuralFeatures().get(3);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcAttribute_Final() {
      return (EAttribute)dbcAttributeEClass.getEStructuralFeatures().get(4);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getAbstractDbcClass() {
      return abstractDbcClassEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getAbstractDbcClass_Constructors() {
      return (EReference)abstractDbcClassEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getAbstractDbcClass_Implements() {
      return (EReference)abstractDbcClassEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getAbstractDbcInterface() {
      return abstractDbcInterfaceEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getAbstractDbcInterface_Methods() {
      return (EReference)abstractDbcInterfaceEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getAbstractDbcInterface_Attributes() {
      return (EReference)abstractDbcInterfaceEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getDbcInterface() {
      return dbcInterfaceEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getDbcInterface_Extends() {
      return (EReference)dbcInterfaceEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getAbstractDbcType() {
      return abstractDbcTypeEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getAbstractDbcType_Name() {
      return (EAttribute)abstractDbcTypeEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getAbstractDbcType_Visibility() {
      return (EAttribute)abstractDbcTypeEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getAbstractDbcType_Static() {
      return (EAttribute)abstractDbcTypeEClass.getEStructuralFeatures().get(2);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getAbstractDbcType_Invariants() {
      return (EReference)abstractDbcTypeEClass.getEStructuralFeatures().get(3);
   }

   /**
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    */
    public EReference getAbstractDbcType_Axioms() {
      return (EReference)abstractDbcTypeEClass.getEStructuralFeatures().get(4);
   }

/**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getAbstractDbcEnum() {
      return abstractDbcEnumEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getAbstractDbcEnum_Literals() {
      return (EReference)abstractDbcEnumEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getDbcEnum() {
      return dbcEnumEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getDbcEnumLiteral() {
      return dbcEnumLiteralEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcEnumLiteral_Name() {
      return (EAttribute)dbcEnumLiteralEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getDbcOperationContract() {
      return dbcOperationContractEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcOperationContract_Pre() {
      return (EAttribute)dbcOperationContractEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcOperationContract_Post() {
      return (EAttribute)dbcOperationContractEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcOperationContract_Modifies() {
      return (EAttribute)dbcOperationContractEClass.getEStructuralFeatures().get(2);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcOperationContract_Termination() {
      return (EAttribute)dbcOperationContractEClass.getEStructuralFeatures().get(3);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getAbstractDbcSpecification() {
      return abstractDbcSpecificationEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getAbstractDbcSpecification_Name() {
      return (EAttribute)abstractDbcSpecificationEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getDbcProperty() {
      return dbcPropertyEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcProperty_Key() {
      return (EAttribute)dbcPropertyEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcProperty_Value() {
      return (EAttribute)dbcPropertyEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getAbstractDbcOperation() {
      return abstractDbcOperationEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getAbstractDbcOperation_OperationContracts() {
      return (EReference)abstractDbcOperationEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getAbstractDbcOperation_Signature() {
      return (EAttribute)abstractDbcOperationEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getAbstractDbcOperation_Visibility() {
      return (EAttribute)abstractDbcOperationEClass.getEStructuralFeatures().get(2);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getAbstractDbcOperation_Static() {
      return (EAttribute)abstractDbcOperationEClass.getEStructuralFeatures().get(3);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getAbstractDbCContainer() {
      return abstractDbCContainerEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getAbstractDbCContainer_Packages() {
      return (EReference)abstractDbCContainerEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getAbstractDbcTypeContainer() {
      return abstractDbcTypeContainerEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getAbstractDbcTypeContainer_Types() {
      return (EReference)abstractDbcTypeContainerEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getIDbCProvable() {
      return iDbCProvableEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getIDbCProvable_ProofObligations() {
      return (EReference)iDbCProvableEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getIDbCProvable_AllProofs() {
      return (EReference)iDbCProvableEClass.getEStructuralFeatures().get(1);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getIDbCProofReferencable() {
      return iDbCProofReferencableEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getIDbCProofReferencable_AllReferences() {
      return (EReference)iDbCProofReferencableEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getDbcProofObligation() {
      return dbcProofObligationEClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbcProofObligation_Obligation() {
      return (EAttribute)dbcProofObligationEClass.getEStructuralFeatures().get(0);
   }

   /**
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    */
    public EClass getDbcAxiom() {
      return dbcAxiomEClass;
   }

/**
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    */
    public EAttribute getDbcAxiom_Definition() {
      return (EAttribute)dbcAxiomEClass.getEStructuralFeatures().get(0);
   }

/**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EReference getDbcAxiom_AxiomContracts() {
      return (EReference)dbcAxiomEClass.getEStructuralFeatures().get(1);
   }

/**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EClass getDbCAxiomContract() {
      return dbCAxiomContractEClass;
   }

/**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbCAxiomContract_Pre() {
      return (EAttribute)dbCAxiomContractEClass.getEStructuralFeatures().get(0);
   }

/**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EAttribute getDbCAxiomContract_Dep() {
      return (EAttribute)dbCAxiomContractEClass.getEStructuralFeatures().get(1);
   }

/**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EEnum getDbcVisibility() {
      return dbcVisibilityEEnum;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EEnum getDbcProofStatus() {
      return dbcProofStatusEEnum;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public EDataType getProperties() {
      return propertiesEDataType;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcmodelFactory getDbcmodelFactory() {
      return (DbcmodelFactory)getEFactoryInstance();
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
      dbcModelEClass = createEClass(DBC_MODEL);
      createEAttribute(dbcModelEClass, DBC_MODEL__DRIVER_ID);
      createEReference(dbcModelEClass, DBC_MODEL__CONNECTION_SETTINGS);
      createEReference(dbcModelEClass, DBC_MODEL__PROOF_OBLIGATIONS);

      dbcPackageEClass = createEClass(DBC_PACKAGE);
      createEAttribute(dbcPackageEClass, DBC_PACKAGE__NAME);

      dbcClassEClass = createEClass(DBC_CLASS);
      createEAttribute(dbcClassEClass, DBC_CLASS__ABSTRACT);
      createEAttribute(dbcClassEClass, DBC_CLASS__FINAL);
      createEReference(dbcClassEClass, DBC_CLASS__EXTENDS);
      createEAttribute(dbcClassEClass, DBC_CLASS__ANONYMOUS);

      abstractDbcProofContainerEClass = createEClass(ABSTRACT_DBC_PROOF_CONTAINER);
      createEReference(abstractDbcProofContainerEClass, ABSTRACT_DBC_PROOF_CONTAINER__PROOFS);

      dbcMethodEClass = createEClass(DBC_METHOD);
      createEAttribute(dbcMethodEClass, DBC_METHOD__RETURN_TYPE);
      createEAttribute(dbcMethodEClass, DBC_METHOD__ABSTRACT);
      createEAttribute(dbcMethodEClass, DBC_METHOD__FINAL);

      dbcInvariantEClass = createEClass(DBC_INVARIANT);
      createEAttribute(dbcInvariantEClass, DBC_INVARIANT__CONDITION);

      dbcProofEClass = createEClass(DBC_PROOF);
      createEReference(dbcProofEClass, DBC_PROOF__TARGET);
      createEReference(dbcProofEClass, DBC_PROOF__PROOF_REFERENCES);
      createEAttribute(dbcProofEClass, DBC_PROOF__OBLIGATION);
      createEAttribute(dbcProofEClass, DBC_PROOF__STATUS);

      dbcConstructorEClass = createEClass(DBC_CONSTRUCTOR);

      dbcProofReferenceEClass = createEClass(DBC_PROOF_REFERENCE);
      createEReference(dbcProofReferenceEClass, DBC_PROOF_REFERENCE__TARGET);
      createEAttribute(dbcProofReferenceEClass, DBC_PROOF_REFERENCE__KIND);
      createEReference(dbcProofReferenceEClass, DBC_PROOF_REFERENCE__SOURCE);

      dbcAttributeEClass = createEClass(DBC_ATTRIBUTE);
      createEAttribute(dbcAttributeEClass, DBC_ATTRIBUTE__NAME);
      createEAttribute(dbcAttributeEClass, DBC_ATTRIBUTE__TYPE);
      createEAttribute(dbcAttributeEClass, DBC_ATTRIBUTE__VISIBILITY);
      createEAttribute(dbcAttributeEClass, DBC_ATTRIBUTE__STATIC);
      createEAttribute(dbcAttributeEClass, DBC_ATTRIBUTE__FINAL);

      abstractDbcClassEClass = createEClass(ABSTRACT_DBC_CLASS);
      createEReference(abstractDbcClassEClass, ABSTRACT_DBC_CLASS__CONSTRUCTORS);
      createEReference(abstractDbcClassEClass, ABSTRACT_DBC_CLASS__IMPLEMENTS);

      abstractDbcInterfaceEClass = createEClass(ABSTRACT_DBC_INTERFACE);
      createEReference(abstractDbcInterfaceEClass, ABSTRACT_DBC_INTERFACE__METHODS);
      createEReference(abstractDbcInterfaceEClass, ABSTRACT_DBC_INTERFACE__ATTRIBUTES);

      dbcInterfaceEClass = createEClass(DBC_INTERFACE);
      createEReference(dbcInterfaceEClass, DBC_INTERFACE__EXTENDS);

      abstractDbcTypeEClass = createEClass(ABSTRACT_DBC_TYPE);
      createEAttribute(abstractDbcTypeEClass, ABSTRACT_DBC_TYPE__NAME);
      createEAttribute(abstractDbcTypeEClass, ABSTRACT_DBC_TYPE__VISIBILITY);
      createEAttribute(abstractDbcTypeEClass, ABSTRACT_DBC_TYPE__STATIC);
      createEReference(abstractDbcTypeEClass, ABSTRACT_DBC_TYPE__INVARIANTS);
      createEReference(abstractDbcTypeEClass, ABSTRACT_DBC_TYPE__AXIOMS);

      abstractDbcEnumEClass = createEClass(ABSTRACT_DBC_ENUM);
      createEReference(abstractDbcEnumEClass, ABSTRACT_DBC_ENUM__LITERALS);

      dbcEnumEClass = createEClass(DBC_ENUM);

      dbcEnumLiteralEClass = createEClass(DBC_ENUM_LITERAL);
      createEAttribute(dbcEnumLiteralEClass, DBC_ENUM_LITERAL__NAME);

      dbcOperationContractEClass = createEClass(DBC_OPERATION_CONTRACT);
      createEAttribute(dbcOperationContractEClass, DBC_OPERATION_CONTRACT__PRE);
      createEAttribute(dbcOperationContractEClass, DBC_OPERATION_CONTRACT__POST);
      createEAttribute(dbcOperationContractEClass, DBC_OPERATION_CONTRACT__MODIFIES);
      createEAttribute(dbcOperationContractEClass, DBC_OPERATION_CONTRACT__TERMINATION);

      abstractDbcSpecificationEClass = createEClass(ABSTRACT_DBC_SPECIFICATION);
      createEAttribute(abstractDbcSpecificationEClass, ABSTRACT_DBC_SPECIFICATION__NAME);

      dbcPropertyEClass = createEClass(DBC_PROPERTY);
      createEAttribute(dbcPropertyEClass, DBC_PROPERTY__KEY);
      createEAttribute(dbcPropertyEClass, DBC_PROPERTY__VALUE);

      abstractDbcOperationEClass = createEClass(ABSTRACT_DBC_OPERATION);
      createEReference(abstractDbcOperationEClass, ABSTRACT_DBC_OPERATION__OPERATION_CONTRACTS);
      createEAttribute(abstractDbcOperationEClass, ABSTRACT_DBC_OPERATION__SIGNATURE);
      createEAttribute(abstractDbcOperationEClass, ABSTRACT_DBC_OPERATION__VISIBILITY);
      createEAttribute(abstractDbcOperationEClass, ABSTRACT_DBC_OPERATION__STATIC);

      abstractDbCContainerEClass = createEClass(ABSTRACT_DB_CCONTAINER);
      createEReference(abstractDbCContainerEClass, ABSTRACT_DB_CCONTAINER__PACKAGES);

      abstractDbcTypeContainerEClass = createEClass(ABSTRACT_DBC_TYPE_CONTAINER);
      createEReference(abstractDbcTypeContainerEClass, ABSTRACT_DBC_TYPE_CONTAINER__TYPES);

      iDbCProvableEClass = createEClass(IDB_CPROVABLE);
      createEReference(iDbCProvableEClass, IDB_CPROVABLE__PROOF_OBLIGATIONS);
      createEReference(iDbCProvableEClass, IDB_CPROVABLE__ALL_PROOFS);

      iDbCProofReferencableEClass = createEClass(IDB_CPROOF_REFERENCABLE);
      createEReference(iDbCProofReferencableEClass, IDB_CPROOF_REFERENCABLE__ALL_REFERENCES);

      dbcProofObligationEClass = createEClass(DBC_PROOF_OBLIGATION);
      createEAttribute(dbcProofObligationEClass, DBC_PROOF_OBLIGATION__OBLIGATION);

      dbcAxiomEClass = createEClass(DBC_AXIOM);
      createEAttribute(dbcAxiomEClass, DBC_AXIOM__DEFINITION);
      createEReference(dbcAxiomEClass, DBC_AXIOM__AXIOM_CONTRACTS);

      dbCAxiomContractEClass = createEClass(DB_CAXIOM_CONTRACT);
      createEAttribute(dbCAxiomContractEClass, DB_CAXIOM_CONTRACT__PRE);
      createEAttribute(dbCAxiomContractEClass, DB_CAXIOM_CONTRACT__DEP);

      // Create enums
      dbcVisibilityEEnum = createEEnum(DBC_VISIBILITY);
      dbcProofStatusEEnum = createEEnum(DBC_PROOF_STATUS);

      // Create data types
      propertiesEDataType = createEDataType(PROPERTIES);
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
      dbcModelEClass.getESuperTypes().add(this.getAbstractDbCContainer());
      dbcPackageEClass.getESuperTypes().add(this.getAbstractDbCContainer());
      dbcClassEClass.getESuperTypes().add(this.getAbstractDbcClass());
      dbcMethodEClass.getESuperTypes().add(this.getAbstractDbcOperation());
      dbcInvariantEClass.getESuperTypes().add(this.getAbstractDbcSpecification());
      dbcInvariantEClass.getESuperTypes().add(this.getIDbCProofReferencable());
      dbcConstructorEClass.getESuperTypes().add(this.getAbstractDbcOperation());
      dbcAttributeEClass.getESuperTypes().add(this.getIDbCProofReferencable());
      abstractDbcClassEClass.getESuperTypes().add(this.getAbstractDbcInterface());
      abstractDbcInterfaceEClass.getESuperTypes().add(this.getAbstractDbcType());
      dbcInterfaceEClass.getESuperTypes().add(this.getAbstractDbcInterface());
      abstractDbcTypeEClass.getESuperTypes().add(this.getAbstractDbcTypeContainer());
      abstractDbcTypeEClass.getESuperTypes().add(this.getIDbCProvable());
      abstractDbcEnumEClass.getESuperTypes().add(this.getAbstractDbcClass());
      dbcEnumEClass.getESuperTypes().add(this.getAbstractDbcEnum());
      dbcEnumLiteralEClass.getESuperTypes().add(this.getIDbCProofReferencable());
      dbcOperationContractEClass.getESuperTypes().add(this.getAbstractDbcSpecification());
      dbcOperationContractEClass.getESuperTypes().add(this.getIDbCProvable());
      abstractDbcOperationEClass.getESuperTypes().add(this.getAbstractDbcProofContainer());
      abstractDbcOperationEClass.getESuperTypes().add(this.getIDbCProvable());
      abstractDbCContainerEClass.getESuperTypes().add(this.getAbstractDbcTypeContainer());
      abstractDbcTypeContainerEClass.getESuperTypes().add(this.getAbstractDbcProofContainer());
      iDbCProvableEClass.getESuperTypes().add(this.getIDbCProofReferencable());
      dbcAxiomEClass.getESuperTypes().add(this.getIDbCProofReferencable());
      dbcAxiomEClass.getESuperTypes().add(this.getAbstractDbcSpecification());
      dbCAxiomContractEClass.getESuperTypes().add(this.getAbstractDbcSpecification());
      dbCAxiomContractEClass.getESuperTypes().add(this.getIDbCProvable());

      // Initialize classes and features; add operations and parameters
      initEClass(dbcModelEClass, DbcModel.class, "DbcModel", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEAttribute(getDbcModel_DriverId(), ecorePackage.getEString(), "driverId", null, 0, 1, DbcModel.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getDbcModel_ConnectionSettings(), this.getDbcProperty(), null, "connectionSettings", null, 0, -1, DbcModel.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getDbcModel_ProofObligations(), this.getDbcProofObligation(), null, "proofObligations", null, 0, -1, DbcModel.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      addEOperation(dbcModelEClass, this.getProperties(), "toConnectionProperties", 0, 1, IS_UNIQUE, IS_ORDERED);

      EOperation op = addEOperation(dbcModelEClass, this.getDbcProofObligation(), "getProofObligation", 0, 1, IS_UNIQUE, IS_ORDERED);
      addEParameter(op, ecorePackage.getEString(), "proofObligation", 0, 1, IS_UNIQUE, IS_ORDERED);

      initEClass(dbcPackageEClass, DbcPackage.class, "DbcPackage", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEAttribute(getDbcPackage_Name(), ecorePackage.getEString(), "name", null, 0, 1, DbcPackage.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(dbcClassEClass, DbcClass.class, "DbcClass", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEAttribute(getDbcClass_Abstract(), ecorePackage.getEBoolean(), "abstract", null, 0, 1, DbcClass.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getDbcClass_Final(), ecorePackage.getEBoolean(), "final", null, 0, 1, DbcClass.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getDbcClass_Extends(), this.getDbcClass(), null, "extends", null, 0, -1, DbcClass.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getDbcClass_Anonymous(), ecorePackage.getEBoolean(), "anonymous", null, 0, 1, DbcClass.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(abstractDbcProofContainerEClass, AbstractDbcProofContainer.class, "AbstractDbcProofContainer", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEReference(getAbstractDbcProofContainer_Proofs(), this.getDbcProof(), null, "proofs", null, 0, -1, AbstractDbcProofContainer.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(dbcMethodEClass, DbcMethod.class, "DbcMethod", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEAttribute(getDbcMethod_ReturnType(), ecorePackage.getEString(), "returnType", null, 0, 1, DbcMethod.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getDbcMethod_Abstract(), ecorePackage.getEBoolean(), "abstract", null, 0, 1, DbcMethod.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getDbcMethod_Final(), ecorePackage.getEBoolean(), "final", null, 0, 1, DbcMethod.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(dbcInvariantEClass, DbcInvariant.class, "DbcInvariant", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEAttribute(getDbcInvariant_Condition(), ecorePackage.getEString(), "condition", null, 0, 1, DbcInvariant.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(dbcProofEClass, DbcProof.class, "DbcProof", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEReference(getDbcProof_Target(), this.getIDbCProvable(), null, "target", null, 0, 1, DbcProof.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getDbcProof_ProofReferences(), this.getDbcProofReference(), null, "proofReferences", null, 0, -1, DbcProof.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getDbcProof_Obligation(), ecorePackage.getEString(), "obligation", null, 0, 1, DbcProof.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getDbcProof_Status(), this.getDbcProofStatus(), "status", "open", 0, 1, DbcProof.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      op = addEOperation(dbcProofEClass, this.getDbcProofReference(), "getProofReference", 0, 1, IS_UNIQUE, IS_ORDERED);
      addEParameter(op, this.getIDbCProofReferencable(), "target", 0, 1, IS_UNIQUE, IS_ORDERED);
      addEParameter(op, ecorePackage.getEString(), "kind", 0, 1, IS_UNIQUE, IS_ORDERED);

      initEClass(dbcConstructorEClass, DbcConstructor.class, "DbcConstructor", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

      initEClass(dbcProofReferenceEClass, DbcProofReference.class, "DbcProofReference", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEReference(getDbcProofReference_Target(), this.getIDbCProofReferencable(), null, "target", null, 0, 1, DbcProofReference.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getDbcProofReference_Kind(), ecorePackage.getEString(), "kind", null, 0, 1, DbcProofReference.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getDbcProofReference_Source(), this.getDbcProof(), null, "source", null, 0, 1, DbcProofReference.class, IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(dbcAttributeEClass, DbcAttribute.class, "DbcAttribute", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEAttribute(getDbcAttribute_Name(), ecorePackage.getEString(), "name", null, 0, 1, DbcAttribute.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getDbcAttribute_Type(), ecorePackage.getEString(), "type", null, 0, 1, DbcAttribute.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getDbcAttribute_Visibility(), this.getDbcVisibility(), "visibility", "private", 0, 1, DbcAttribute.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getDbcAttribute_Static(), ecorePackage.getEBoolean(), "static", null, 0, 1, DbcAttribute.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getDbcAttribute_Final(), ecorePackage.getEBoolean(), "final", null, 0, 1, DbcAttribute.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(abstractDbcClassEClass, AbstractDbcClass.class, "AbstractDbcClass", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEReference(getAbstractDbcClass_Constructors(), this.getDbcConstructor(), null, "constructors", null, 0, -1, AbstractDbcClass.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getAbstractDbcClass_Implements(), this.getDbcInterface(), null, "implements", null, 0, -1, AbstractDbcClass.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      op = addEOperation(abstractDbcClassEClass, this.getDbcConstructor(), "getConstructor", 0, 1, IS_UNIQUE, IS_ORDERED);
      addEParameter(op, ecorePackage.getEString(), "signature", 0, 1, IS_UNIQUE, IS_ORDERED);

      initEClass(abstractDbcInterfaceEClass, AbstractDbcInterface.class, "AbstractDbcInterface", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEReference(getAbstractDbcInterface_Methods(), this.getDbcMethod(), null, "methods", null, 0, -1, AbstractDbcInterface.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getAbstractDbcInterface_Attributes(), this.getDbcAttribute(), null, "attributes", null, 0, -1, AbstractDbcInterface.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      op = addEOperation(abstractDbcInterfaceEClass, this.getDbcMethod(), "getMethod", 0, 1, IS_UNIQUE, IS_ORDERED);
      addEParameter(op, ecorePackage.getEString(), "signature", 0, 1, IS_UNIQUE, IS_ORDERED);

      op = addEOperation(abstractDbcInterfaceEClass, this.getDbcAttribute(), "getAttribute", 0, 1, IS_UNIQUE, IS_ORDERED);
      addEParameter(op, ecorePackage.getEString(), "name", 0, 1, IS_UNIQUE, IS_ORDERED);

      initEClass(dbcInterfaceEClass, DbcInterface.class, "DbcInterface", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEReference(getDbcInterface_Extends(), this.getDbcInterface(), null, "extends", null, 0, -1, DbcInterface.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(abstractDbcTypeEClass, AbstractDbcType.class, "AbstractDbcType", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEAttribute(getAbstractDbcType_Name(), ecorePackage.getEString(), "name", null, 0, 1, AbstractDbcType.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getAbstractDbcType_Visibility(), this.getDbcVisibility(), "visibility", "public", 0, 1, AbstractDbcType.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getAbstractDbcType_Static(), ecorePackage.getEBoolean(), "static", null, 0, 1, AbstractDbcType.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getAbstractDbcType_Invariants(), this.getDbcInvariant(), null, "invariants", null, 0, -1, AbstractDbcType.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getAbstractDbcType_Axioms(), this.getDbcAxiom(), null, "axioms", null, 0, -1, AbstractDbcType.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      op = addEOperation(abstractDbcTypeEClass, this.getDbcInvariant(), "getInvariant", 0, 1, IS_UNIQUE, IS_ORDERED);
      addEParameter(op, ecorePackage.getEString(), "condition", 0, 1, IS_UNIQUE, IS_ORDERED);

      op = addEOperation(abstractDbcTypeEClass, this.getDbcAxiom(), "getAxiom", 0, 1, IS_UNIQUE, IS_ORDERED);
      addEParameter(op, ecorePackage.getEString(), "definition", 0, 1, IS_UNIQUE, IS_ORDERED);

      initEClass(abstractDbcEnumEClass, AbstractDbcEnum.class, "AbstractDbcEnum", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEReference(getAbstractDbcEnum_Literals(), this.getDbcEnumLiteral(), null, "literals", null, 0, -1, AbstractDbcEnum.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      op = addEOperation(abstractDbcEnumEClass, this.getDbcEnumLiteral(), "getLiteral", 0, 1, IS_UNIQUE, IS_ORDERED);
      addEParameter(op, ecorePackage.getEString(), "name", 0, 1, IS_UNIQUE, IS_ORDERED);

      initEClass(dbcEnumEClass, DbcEnum.class, "DbcEnum", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);

      initEClass(dbcEnumLiteralEClass, DbcEnumLiteral.class, "DbcEnumLiteral", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEAttribute(getDbcEnumLiteral_Name(), ecorePackage.getEString(), "name", null, 0, 1, DbcEnumLiteral.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(dbcOperationContractEClass, DbcOperationContract.class, "DbcOperationContract", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEAttribute(getDbcOperationContract_Pre(), ecorePackage.getEString(), "pre", null, 0, 1, DbcOperationContract.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getDbcOperationContract_Post(), ecorePackage.getEString(), "post", null, 0, 1, DbcOperationContract.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getDbcOperationContract_Modifies(), ecorePackage.getEString(), "modifies", null, 0, 1, DbcOperationContract.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getDbcOperationContract_Termination(), ecorePackage.getEString(), "termination", null, 0, 1, DbcOperationContract.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(abstractDbcSpecificationEClass, AbstractDbcSpecification.class, "AbstractDbcSpecification", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEAttribute(getAbstractDbcSpecification_Name(), ecorePackage.getEString(), "name", null, 0, 1, AbstractDbcSpecification.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(dbcPropertyEClass, DbcProperty.class, "DbcProperty", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEAttribute(getDbcProperty_Key(), ecorePackage.getEString(), "key", null, 0, 1, DbcProperty.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getDbcProperty_Value(), ecorePackage.getEString(), "value", null, 0, 1, DbcProperty.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(abstractDbcOperationEClass, AbstractDbcOperation.class, "AbstractDbcOperation", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEReference(getAbstractDbcOperation_OperationContracts(), this.getDbcOperationContract(), null, "operationContracts", null, 0, -1, AbstractDbcOperation.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getAbstractDbcOperation_Signature(), ecorePackage.getEString(), "signature", null, 0, 1, AbstractDbcOperation.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getAbstractDbcOperation_Visibility(), this.getDbcVisibility(), "visibility", "public", 0, 1, AbstractDbcOperation.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getAbstractDbcOperation_Static(), ecorePackage.getEBoolean(), "static", null, 0, 1, AbstractDbcOperation.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      op = addEOperation(abstractDbcOperationEClass, this.getDbcOperationContract(), "getOperationContract", 0, 1, IS_UNIQUE, IS_ORDERED);
      addEParameter(op, ecorePackage.getEString(), "pre", 0, 1, IS_UNIQUE, IS_ORDERED);
      addEParameter(op, ecorePackage.getEString(), "post", 0, 1, IS_UNIQUE, IS_ORDERED);

      initEClass(abstractDbCContainerEClass, AbstractDbCContainer.class, "AbstractDbCContainer", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEReference(getAbstractDbCContainer_Packages(), this.getDbcPackage(), null, "packages", null, 0, -1, AbstractDbCContainer.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      op = addEOperation(abstractDbCContainerEClass, this.getDbcPackage(), "getPackage", 0, 1, IS_UNIQUE, IS_ORDERED);
      addEParameter(op, ecorePackage.getEString(), "name", 0, 1, IS_UNIQUE, IS_ORDERED);

      initEClass(abstractDbcTypeContainerEClass, AbstractDbcTypeContainer.class, "AbstractDbcTypeContainer", IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEReference(getAbstractDbcTypeContainer_Types(), this.getAbstractDbcType(), null, "types", null, 0, -1, AbstractDbcTypeContainer.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      op = addEOperation(abstractDbcTypeContainerEClass, this.getAbstractDbcType(), "getType", 0, 1, IS_UNIQUE, IS_ORDERED);
      addEParameter(op, ecorePackage.getEString(), "name", 0, 1, IS_UNIQUE, IS_ORDERED);

      initEClass(iDbCProvableEClass, IDbCProvable.class, "IDbCProvable", IS_ABSTRACT, IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEReference(getIDbCProvable_ProofObligations(), this.getDbcProofObligation(), null, "proofObligations", null, 0, -1, IDbCProvable.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getIDbCProvable_AllProofs(), this.getDbcProof(), null, "allProofs", null, 0, -1, IDbCProvable.class, IS_TRANSIENT, !IS_VOLATILE, !IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(iDbCProofReferencableEClass, IDbCProofReferencable.class, "IDbCProofReferencable", IS_ABSTRACT, IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEReference(getIDbCProofReferencable_AllReferences(), this.getDbcProofReference(), null, "allReferences", null, 0, -1, IDbCProofReferencable.class, IS_TRANSIENT, !IS_VOLATILE, !IS_CHANGEABLE, !IS_COMPOSITE, IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(dbcProofObligationEClass, DbcProofObligation.class, "DbcProofObligation", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEAttribute(getDbcProofObligation_Obligation(), ecorePackage.getEString(), "obligation", null, 0, 1, DbcProofObligation.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      initEClass(dbcAxiomEClass, DbcAxiom.class, "DbcAxiom", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEAttribute(getDbcAxiom_Definition(), ecorePackage.getEString(), "definition", null, 0, 1, DbcAxiom.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEReference(getDbcAxiom_AxiomContracts(), this.getDbCAxiomContract(), null, "axiomContracts", null, 0, -1, DbcAxiom.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, IS_COMPOSITE, !IS_RESOLVE_PROXIES, !IS_UNSETTABLE, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      op = addEOperation(dbcAxiomEClass, this.getDbCAxiomContract(), "getAxiomContract", 0, 1, IS_UNIQUE, IS_ORDERED);
      addEParameter(op, ecorePackage.getEString(), "pre", 0, 1, IS_UNIQUE, IS_ORDERED);
      addEParameter(op, ecorePackage.getEString(), "dep", 0, 1, IS_UNIQUE, IS_ORDERED);

      initEClass(dbCAxiomContractEClass, DbCAxiomContract.class, "DbCAxiomContract", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
      initEAttribute(getDbCAxiomContract_Pre(), ecorePackage.getEString(), "pre", null, 0, 1, DbCAxiomContract.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
      initEAttribute(getDbCAxiomContract_Dep(), ecorePackage.getEString(), "dep", null, 0, 1, DbCAxiomContract.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

      // Initialize enums and add enum literals
      initEEnum(dbcVisibilityEEnum, DbcVisibility.class, "DbcVisibility");
      addEEnumLiteral(dbcVisibilityEEnum, DbcVisibility.DEFAULT);
      addEEnumLiteral(dbcVisibilityEEnum, DbcVisibility.PRIVATE);
      addEEnumLiteral(dbcVisibilityEEnum, DbcVisibility.PROTECTED);
      addEEnumLiteral(dbcVisibilityEEnum, DbcVisibility.PUBLIC);

      initEEnum(dbcProofStatusEEnum, DbcProofStatus.class, "DbcProofStatus");
      addEEnumLiteral(dbcProofStatusEEnum, DbcProofStatus.FAILED);
      addEEnumLiteral(dbcProofStatusEEnum, DbcProofStatus.OPEN);
      addEEnumLiteral(dbcProofStatusEEnum, DbcProofStatus.FULFILLED);

      // Initialize data types
      initEDataType(propertiesEDataType, Properties.class, "Properties", IS_SERIALIZABLE, !IS_GENERATED_INSTANCE_CLASS);

      // Create resource
      createResource(eNS_URI);
   }

} //DbcmodelPackageImpl