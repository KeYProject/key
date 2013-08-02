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

import de.hentschel.visualdbc.dbcmodel.*;
import java.util.Properties;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EDataType;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.impl.EFactoryImpl;
import org.eclipse.emf.ecore.plugin.EcorePlugin;


/**
 * <!-- begin-user-doc -->
 * An implementation of the model <b>Factory</b>.
 * <!-- end-user-doc -->
 * @generated
 */
public class DbcmodelFactoryImpl extends EFactoryImpl implements DbcmodelFactory {
   /**
    * Creates the default factory implementation.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public static DbcmodelFactory init() {
      try {
         DbcmodelFactory theDbcmodelFactory = (DbcmodelFactory)EPackage.Registry.INSTANCE.getEFactory("http://www.hentschel.de/dbcmodel"); 
         if (theDbcmodelFactory != null) {
            return theDbcmodelFactory;
         }
      }
      catch (Exception exception) {
         EcorePlugin.INSTANCE.log(exception);
      }
      return new DbcmodelFactoryImpl();
   }

   /**
    * Creates an instance of the factory.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcmodelFactoryImpl() {
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
         case DbcmodelPackage.DBC_MODEL: return createDbcModel();
         case DbcmodelPackage.DBC_PACKAGE: return createDbcPackage();
         case DbcmodelPackage.DBC_CLASS: return createDbcClass();
         case DbcmodelPackage.DBC_METHOD: return createDbcMethod();
         case DbcmodelPackage.DBC_INVARIANT: return createDbcInvariant();
         case DbcmodelPackage.DBC_PROOF: return createDbcProof();
         case DbcmodelPackage.DBC_CONSTRUCTOR: return createDbcConstructor();
         case DbcmodelPackage.DBC_PROOF_REFERENCE: return createDbcProofReference();
         case DbcmodelPackage.DBC_ATTRIBUTE: return createDbcAttribute();
         case DbcmodelPackage.DBC_INTERFACE: return createDbcInterface();
         case DbcmodelPackage.DBC_ENUM: return createDbcEnum();
         case DbcmodelPackage.DBC_ENUM_LITERAL: return createDbcEnumLiteral();
         case DbcmodelPackage.DBC_OPERATION_CONTRACT: return createDbcOperationContract();
         case DbcmodelPackage.DBC_PROPERTY: return createDbcProperty();
         case DbcmodelPackage.DBC_PROOF_OBLIGATION: return createDbcProofObligation();
         case DbcmodelPackage.DBC_AXIOM: return createDbcAxiom();
         case DbcmodelPackage.DB_CAXIOM_CONTRACT: return createDbCAxiomContract();
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
         case DbcmodelPackage.DBC_VISIBILITY:
            return createDbcVisibilityFromString(eDataType, initialValue);
         case DbcmodelPackage.DBC_PROOF_STATUS:
            return createDbcProofStatusFromString(eDataType, initialValue);
         case DbcmodelPackage.PROPERTIES:
            return createPropertiesFromString(eDataType, initialValue);
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
         case DbcmodelPackage.DBC_VISIBILITY:
            return convertDbcVisibilityToString(eDataType, instanceValue);
         case DbcmodelPackage.DBC_PROOF_STATUS:
            return convertDbcProofStatusToString(eDataType, instanceValue);
         case DbcmodelPackage.PROPERTIES:
            return convertPropertiesToString(eDataType, instanceValue);
         default:
            throw new IllegalArgumentException("The datatype '" + eDataType.getName() + "' is not a valid classifier");
      }
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcModel createDbcModel() {
      DbcModelImpl dbcModel = new DbcModelImpl();
      return dbcModel;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcPackage createDbcPackage() {
      DbcPackageImpl dbcPackage = new DbcPackageImpl();
      return dbcPackage;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcClass createDbcClass() {
      DbcClassImpl dbcClass = new DbcClassImpl();
      return dbcClass;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcMethod createDbcMethod() {
      DbcMethodImpl dbcMethod = new DbcMethodImpl();
      return dbcMethod;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcInvariant createDbcInvariant() {
      DbcInvariantImpl dbcInvariant = new DbcInvariantImpl();
      return dbcInvariant;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcProof createDbcProof() {
      DbcProofImpl dbcProof = new DbcProofImpl();
      return dbcProof;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcConstructor createDbcConstructor() {
      DbcConstructorImpl dbcConstructor = new DbcConstructorImpl();
      return dbcConstructor;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcProofReference createDbcProofReference() {
      DbcProofReferenceImpl dbcProofReference = new DbcProofReferenceImpl();
      return dbcProofReference;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcAttribute createDbcAttribute() {
      DbcAttributeImpl dbcAttribute = new DbcAttributeImpl();
      return dbcAttribute;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcInterface createDbcInterface() {
      DbcInterfaceImpl dbcInterface = new DbcInterfaceImpl();
      return dbcInterface;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcEnum createDbcEnum() {
      DbcEnumImpl dbcEnum = new DbcEnumImpl();
      return dbcEnum;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcEnumLiteral createDbcEnumLiteral() {
      DbcEnumLiteralImpl dbcEnumLiteral = new DbcEnumLiteralImpl();
      return dbcEnumLiteral;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcOperationContract createDbcOperationContract() {
      DbcOperationContractImpl dbcOperationContract = new DbcOperationContractImpl();
      return dbcOperationContract;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcProperty createDbcProperty() {
      DbcPropertyImpl dbcProperty = new DbcPropertyImpl();
      return dbcProperty;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcProofObligation createDbcProofObligation() {
      DbcProofObligationImpl dbcProofObligation = new DbcProofObligationImpl();
      return dbcProofObligation;
   }

   /**
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    */
    public DbcAxiom createDbcAxiom() {
      DbcAxiomImpl dbcAxiom = new DbcAxiomImpl();
      return dbcAxiom;
   }

/**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbCAxiomContract createDbCAxiomContract() {
      DbCAxiomContractImpl dbCAxiomContract = new DbCAxiomContractImpl();
      return dbCAxiomContract;
   }

/**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcVisibility createDbcVisibilityFromString(EDataType eDataType, String initialValue) {
      DbcVisibility result = DbcVisibility.get(initialValue);
      if (result == null) throw new IllegalArgumentException("The value '" + initialValue + "' is not a valid enumerator of '" + eDataType.getName() + "'");
      return result;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String convertDbcVisibilityToString(EDataType eDataType, Object instanceValue) {
      return instanceValue == null ? null : instanceValue.toString();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcProofStatus createDbcProofStatusFromString(EDataType eDataType, String initialValue) {
      DbcProofStatus result = DbcProofStatus.get(initialValue);
      if (result == null) throw new IllegalArgumentException("The value '" + initialValue + "' is not a valid enumerator of '" + eDataType.getName() + "'");
      return result;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String convertDbcProofStatusToString(EDataType eDataType, Object instanceValue) {
      return instanceValue == null ? null : instanceValue.toString();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public Properties createPropertiesFromString(EDataType eDataType, String initialValue) {
      return (Properties)super.createFromString(eDataType, initialValue);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public String convertPropertiesToString(EDataType eDataType, Object instanceValue) {
      return super.convertToString(eDataType, instanceValue);
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcmodelPackage getDbcmodelPackage() {
      return (DbcmodelPackage)getEPackage();
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @deprecated
    * @generated
    */
   @Deprecated
   public static DbcmodelPackage getPackage() {
      return DbcmodelPackage.eINSTANCE;
   }

} //DbcmodelFactoryImpl