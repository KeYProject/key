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
package de.hentschel.visualdbc.dbcmodel.util;

import de.hentschel.visualdbc.dbcmodel.*;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.util.Switch;

import de.hentschel.visualdbc.dbcmodel.AbstractDbCContainer;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcClass;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcEnum;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcInterface;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcProofContainer;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcSpecification;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcType;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcTypeContainer;
import de.hentschel.visualdbc.dbcmodel.DbcAttribute;
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
import de.hentschel.visualdbc.dbcmodel.DbcProperty;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
import de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable;
import de.hentschel.visualdbc.dbcmodel.IDbCProvable;

/**
 * <!-- begin-user-doc -->
 * The <b>Switch</b> for the model's inheritance hierarchy.
 * It supports the call {@link #doSwitch(EObject) doSwitch(object)}
 * to invoke the <code>caseXXX</code> method for each class of the model,
 * starting with the actual class of the object
 * and proceeding up the inheritance hierarchy
 * until a non-null result is returned,
 * which is the result of the switch.
 * <!-- end-user-doc -->
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage
 * @generated
 */
public class DbcmodelSwitch<T> extends Switch<T> {
   /**
    * The cached model package
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected static DbcmodelPackage modelPackage;

   /**
    * Creates an instance of the switch.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcmodelSwitch() {
      if (modelPackage == null) {
         modelPackage = DbcmodelPackage.eINSTANCE;
      }
   }

   /**
    * Checks whether this is a switch for the given package.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @parameter ePackage the package in question.
    * @return whether this is a switch for the given package.
    * @generated
    */
   @Override
   protected boolean isSwitchFor(EPackage ePackage) {
      return ePackage == modelPackage;
   }

   /**
    * Calls <code>caseXXX</code> for each class of the model until one returns a non null result; it yields that result.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the first non-null result returned by a <code>caseXXX</code> call.
    * @generated
    */
   @Override
   protected T doSwitch(int classifierID, EObject theEObject) {
      switch (classifierID) {
         case DbcmodelPackage.DBC_MODEL: {
            DbcModel dbcModel = (DbcModel)theEObject;
            T result = caseDbcModel(dbcModel);
            if (result == null) result = caseAbstractDbCContainer(dbcModel);
            if (result == null) result = caseAbstractDbcTypeContainer(dbcModel);
            if (result == null) result = caseAbstractDbcProofContainer(dbcModel);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.DBC_PACKAGE: {
            DbcPackage dbcPackage = (DbcPackage)theEObject;
            T result = caseDbcPackage(dbcPackage);
            if (result == null) result = caseAbstractDbCContainer(dbcPackage);
            if (result == null) result = caseAbstractDbcTypeContainer(dbcPackage);
            if (result == null) result = caseAbstractDbcProofContainer(dbcPackage);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.DBC_CLASS: {
            DbcClass dbcClass = (DbcClass)theEObject;
            T result = caseDbcClass(dbcClass);
            if (result == null) result = caseAbstractDbcClass(dbcClass);
            if (result == null) result = caseAbstractDbcInterface(dbcClass);
            if (result == null) result = caseAbstractDbcType(dbcClass);
            if (result == null) result = caseAbstractDbcTypeContainer(dbcClass);
            if (result == null) result = caseIDbCProvable(dbcClass);
            if (result == null) result = caseAbstractDbcProofContainer(dbcClass);
            if (result == null) result = caseIDbCProofReferencable(dbcClass);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.ABSTRACT_DBC_PROOF_CONTAINER: {
            AbstractDbcProofContainer abstractDbcProofContainer = (AbstractDbcProofContainer)theEObject;
            T result = caseAbstractDbcProofContainer(abstractDbcProofContainer);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.DBC_METHOD: {
            DbcMethod dbcMethod = (DbcMethod)theEObject;
            T result = caseDbcMethod(dbcMethod);
            if (result == null) result = caseAbstractDbcOperation(dbcMethod);
            if (result == null) result = caseAbstractDbcProofContainer(dbcMethod);
            if (result == null) result = caseIDbCProvable(dbcMethod);
            if (result == null) result = caseIDbCProofReferencable(dbcMethod);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.DBC_INVARIANT: {
            DbcInvariant dbcInvariant = (DbcInvariant)theEObject;
            T result = caseDbcInvariant(dbcInvariant);
            if (result == null) result = caseAbstractDbcSpecification(dbcInvariant);
            if (result == null) result = caseIDbCProofReferencable(dbcInvariant);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.DBC_PROOF: {
            DbcProof dbcProof = (DbcProof)theEObject;
            T result = caseDbcProof(dbcProof);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.DBC_CONSTRUCTOR: {
            DbcConstructor dbcConstructor = (DbcConstructor)theEObject;
            T result = caseDbcConstructor(dbcConstructor);
            if (result == null) result = caseAbstractDbcOperation(dbcConstructor);
            if (result == null) result = caseAbstractDbcProofContainer(dbcConstructor);
            if (result == null) result = caseIDbCProvable(dbcConstructor);
            if (result == null) result = caseIDbCProofReferencable(dbcConstructor);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.DBC_PROOF_REFERENCE: {
            DbcProofReference dbcProofReference = (DbcProofReference)theEObject;
            T result = caseDbcProofReference(dbcProofReference);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.DBC_ATTRIBUTE: {
            DbcAttribute dbcAttribute = (DbcAttribute)theEObject;
            T result = caseDbcAttribute(dbcAttribute);
            if (result == null) result = caseIDbCProofReferencable(dbcAttribute);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.ABSTRACT_DBC_CLASS: {
            AbstractDbcClass abstractDbcClass = (AbstractDbcClass)theEObject;
            T result = caseAbstractDbcClass(abstractDbcClass);
            if (result == null) result = caseAbstractDbcInterface(abstractDbcClass);
            if (result == null) result = caseAbstractDbcType(abstractDbcClass);
            if (result == null) result = caseAbstractDbcTypeContainer(abstractDbcClass);
            if (result == null) result = caseIDbCProvable(abstractDbcClass);
            if (result == null) result = caseAbstractDbcProofContainer(abstractDbcClass);
            if (result == null) result = caseIDbCProofReferencable(abstractDbcClass);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.ABSTRACT_DBC_INTERFACE: {
            AbstractDbcInterface abstractDbcInterface = (AbstractDbcInterface)theEObject;
            T result = caseAbstractDbcInterface(abstractDbcInterface);
            if (result == null) result = caseAbstractDbcType(abstractDbcInterface);
            if (result == null) result = caseAbstractDbcTypeContainer(abstractDbcInterface);
            if (result == null) result = caseIDbCProvable(abstractDbcInterface);
            if (result == null) result = caseAbstractDbcProofContainer(abstractDbcInterface);
            if (result == null) result = caseIDbCProofReferencable(abstractDbcInterface);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.DBC_INTERFACE: {
            DbcInterface dbcInterface = (DbcInterface)theEObject;
            T result = caseDbcInterface(dbcInterface);
            if (result == null) result = caseAbstractDbcInterface(dbcInterface);
            if (result == null) result = caseAbstractDbcType(dbcInterface);
            if (result == null) result = caseAbstractDbcTypeContainer(dbcInterface);
            if (result == null) result = caseIDbCProvable(dbcInterface);
            if (result == null) result = caseAbstractDbcProofContainer(dbcInterface);
            if (result == null) result = caseIDbCProofReferencable(dbcInterface);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.ABSTRACT_DBC_TYPE: {
            AbstractDbcType abstractDbcType = (AbstractDbcType)theEObject;
            T result = caseAbstractDbcType(abstractDbcType);
            if (result == null) result = caseAbstractDbcTypeContainer(abstractDbcType);
            if (result == null) result = caseIDbCProvable(abstractDbcType);
            if (result == null) result = caseAbstractDbcProofContainer(abstractDbcType);
            if (result == null) result = caseIDbCProofReferencable(abstractDbcType);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.ABSTRACT_DBC_ENUM: {
            AbstractDbcEnum abstractDbcEnum = (AbstractDbcEnum)theEObject;
            T result = caseAbstractDbcEnum(abstractDbcEnum);
            if (result == null) result = caseAbstractDbcClass(abstractDbcEnum);
            if (result == null) result = caseAbstractDbcInterface(abstractDbcEnum);
            if (result == null) result = caseAbstractDbcType(abstractDbcEnum);
            if (result == null) result = caseAbstractDbcTypeContainer(abstractDbcEnum);
            if (result == null) result = caseIDbCProvable(abstractDbcEnum);
            if (result == null) result = caseAbstractDbcProofContainer(abstractDbcEnum);
            if (result == null) result = caseIDbCProofReferencable(abstractDbcEnum);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.DBC_ENUM: {
            DbcEnum dbcEnum = (DbcEnum)theEObject;
            T result = caseDbcEnum(dbcEnum);
            if (result == null) result = caseAbstractDbcEnum(dbcEnum);
            if (result == null) result = caseAbstractDbcClass(dbcEnum);
            if (result == null) result = caseAbstractDbcInterface(dbcEnum);
            if (result == null) result = caseAbstractDbcType(dbcEnum);
            if (result == null) result = caseAbstractDbcTypeContainer(dbcEnum);
            if (result == null) result = caseIDbCProvable(dbcEnum);
            if (result == null) result = caseAbstractDbcProofContainer(dbcEnum);
            if (result == null) result = caseIDbCProofReferencable(dbcEnum);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.DBC_ENUM_LITERAL: {
            DbcEnumLiteral dbcEnumLiteral = (DbcEnumLiteral)theEObject;
            T result = caseDbcEnumLiteral(dbcEnumLiteral);
            if (result == null) result = caseIDbCProofReferencable(dbcEnumLiteral);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.DBC_OPERATION_CONTRACT: {
            DbcOperationContract dbcOperationContract = (DbcOperationContract)theEObject;
            T result = caseDbcOperationContract(dbcOperationContract);
            if (result == null) result = caseAbstractDbcSpecification(dbcOperationContract);
            if (result == null) result = caseIDbCProvable(dbcOperationContract);
            if (result == null) result = caseIDbCProofReferencable(dbcOperationContract);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.ABSTRACT_DBC_SPECIFICATION: {
            AbstractDbcSpecification abstractDbcSpecification = (AbstractDbcSpecification)theEObject;
            T result = caseAbstractDbcSpecification(abstractDbcSpecification);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.DBC_PROPERTY: {
            DbcProperty dbcProperty = (DbcProperty)theEObject;
            T result = caseDbcProperty(dbcProperty);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.ABSTRACT_DBC_OPERATION: {
            AbstractDbcOperation abstractDbcOperation = (AbstractDbcOperation)theEObject;
            T result = caseAbstractDbcOperation(abstractDbcOperation);
            if (result == null) result = caseAbstractDbcProofContainer(abstractDbcOperation);
            if (result == null) result = caseIDbCProvable(abstractDbcOperation);
            if (result == null) result = caseIDbCProofReferencable(abstractDbcOperation);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.ABSTRACT_DB_CCONTAINER: {
            AbstractDbCContainer abstractDbCContainer = (AbstractDbCContainer)theEObject;
            T result = caseAbstractDbCContainer(abstractDbCContainer);
            if (result == null) result = caseAbstractDbcTypeContainer(abstractDbCContainer);
            if (result == null) result = caseAbstractDbcProofContainer(abstractDbCContainer);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.ABSTRACT_DBC_TYPE_CONTAINER: {
            AbstractDbcTypeContainer abstractDbcTypeContainer = (AbstractDbcTypeContainer)theEObject;
            T result = caseAbstractDbcTypeContainer(abstractDbcTypeContainer);
            if (result == null) result = caseAbstractDbcProofContainer(abstractDbcTypeContainer);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.IDB_CPROVABLE: {
            IDbCProvable iDbCProvable = (IDbCProvable)theEObject;
            T result = caseIDbCProvable(iDbCProvable);
            if (result == null) result = caseIDbCProofReferencable(iDbCProvable);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.IDB_CPROOF_REFERENCABLE: {
            IDbCProofReferencable iDbCProofReferencable = (IDbCProofReferencable)theEObject;
            T result = caseIDbCProofReferencable(iDbCProofReferencable);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.DBC_PROOF_OBLIGATION: {
            DbcProofObligation dbcProofObligation = (DbcProofObligation)theEObject;
            T result = caseDbcProofObligation(dbcProofObligation);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.DBC_AXIOM: {
            DbcAxiom dbcAxiom = (DbcAxiom)theEObject;
            T result = caseDbcAxiom(dbcAxiom);
            if (result == null) result = caseIDbCProofReferencable(dbcAxiom);
            if (result == null) result = caseAbstractDbcSpecification(dbcAxiom);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DbcmodelPackage.DB_CAXIOM_CONTRACT: {
            DbCAxiomContract dbCAxiomContract = (DbCAxiomContract)theEObject;
            T result = caseDbCAxiomContract(dbCAxiomContract);
            if (result == null) result = caseAbstractDbcSpecification(dbCAxiomContract);
            if (result == null) result = caseIDbCProvable(dbCAxiomContract);
            if (result == null) result = caseIDbCProofReferencable(dbCAxiomContract);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         default: return defaultCase(theEObject);
      }
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Dbc Model</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Dbc Model</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseDbcModel(DbcModel object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Dbc Package</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Dbc Package</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseDbcPackage(DbcPackage object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Dbc Class</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Dbc Class</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseDbcClass(DbcClass object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Abstract Dbc Proof Container</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Abstract Dbc Proof Container</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseAbstractDbcProofContainer(AbstractDbcProofContainer object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Dbc Method</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Dbc Method</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseDbcMethod(DbcMethod object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Dbc Invariant</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Dbc Invariant</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseDbcInvariant(DbcInvariant object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Dbc Proof</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Dbc Proof</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseDbcProof(DbcProof object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Dbc Constructor</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Dbc Constructor</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseDbcConstructor(DbcConstructor object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Dbc Proof Reference</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Dbc Proof Reference</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseDbcProofReference(DbcProofReference object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Dbc Attribute</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Dbc Attribute</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseDbcAttribute(DbcAttribute object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Abstract Dbc Class</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Abstract Dbc Class</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseAbstractDbcClass(AbstractDbcClass object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Abstract Dbc Interface</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Abstract Dbc Interface</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseAbstractDbcInterface(AbstractDbcInterface object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Dbc Interface</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Dbc Interface</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseDbcInterface(DbcInterface object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Abstract Dbc Type</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Abstract Dbc Type</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseAbstractDbcType(AbstractDbcType object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Abstract Dbc Enum</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Abstract Dbc Enum</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseAbstractDbcEnum(AbstractDbcEnum object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Dbc Enum</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Dbc Enum</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseDbcEnum(DbcEnum object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Dbc Enum Literal</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Dbc Enum Literal</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseDbcEnumLiteral(DbcEnumLiteral object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Dbc Operation Contract</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Dbc Operation Contract</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseDbcOperationContract(DbcOperationContract object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Abstract Dbc Specification</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Abstract Dbc Specification</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseAbstractDbcSpecification(AbstractDbcSpecification object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Dbc Property</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Dbc Property</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseDbcProperty(DbcProperty object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Abstract Dbc Operation</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Abstract Dbc Operation</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseAbstractDbcOperation(AbstractDbcOperation object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Abstract Db CContainer</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Abstract Db CContainer</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseAbstractDbCContainer(AbstractDbCContainer object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Abstract Dbc Type Container</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Abstract Dbc Type Container</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseAbstractDbcTypeContainer(AbstractDbcTypeContainer object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>IDb CProvable</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>IDb CProvable</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseIDbCProvable(IDbCProvable object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>IDb CProof Referencable</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>IDb CProof Referencable</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseIDbCProofReferencable(IDbCProofReferencable object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Dbc Proof Obligation</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Dbc Proof Obligation</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseDbcProofObligation(DbcProofObligation object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Dbc Axiom</em>'.
    * <!-- begin-user-doc -->
     * This implementation returns null;
     * returning a non-null result will terminate the switch.
     * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Dbc Axiom</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
    public T caseDbcAxiom(DbcAxiom object) {
      return null;
   }

/**
    * Returns the result of interpreting the object as an instance of '<em>Db CAxiom Contract</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Db CAxiom Contract</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseDbCAxiomContract(DbCAxiomContract object) {
      return null;
   }

/**
    * Returns the result of interpreting the object as an instance of '<em>EObject</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch, but this is the last case anyway.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>EObject</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject)
    * @generated
    */
   @Override
   public T defaultCase(EObject object) {
      return null;
   }

} //DbcmodelSwitch