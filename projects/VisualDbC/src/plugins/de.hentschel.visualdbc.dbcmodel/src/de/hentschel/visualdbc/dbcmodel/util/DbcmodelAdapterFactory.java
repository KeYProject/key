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
package de.hentschel.visualdbc.dbcmodel.util;

import de.hentschel.visualdbc.dbcmodel.*;

import org.eclipse.emf.common.notify.Adapter;
import org.eclipse.emf.common.notify.Notifier;

import org.eclipse.emf.common.notify.impl.AdapterFactoryImpl;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * The <b>Adapter Factory</b> for the model.
 * It provides an adapter <code>createXXX</code> method for each class of the model.
 * <!-- end-user-doc -->
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage
 * @generated
 */
public class DbcmodelAdapterFactory extends AdapterFactoryImpl {
   /**
    * The cached model package.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected static DbcmodelPackage modelPackage;

   /**
    * Creates an instance of the adapter factory.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcmodelAdapterFactory() {
      if (modelPackage == null) {
         modelPackage = DbcmodelPackage.eINSTANCE;
      }
   }

   /**
    * Returns whether this factory is applicable for the type of the object.
    * <!-- begin-user-doc -->
    * This implementation returns <code>true</code> if the object is either the model's package or is an instance object of the model.
    * <!-- end-user-doc -->
    * @return whether this factory is applicable for the type of the object.
    * @generated
    */
   @Override
   public boolean isFactoryForType(Object object) {
      if (object == modelPackage) {
         return true;
      }
      if (object instanceof EObject) {
         return ((EObject)object).eClass().getEPackage() == modelPackage;
      }
      return false;
   }

   /**
    * The switch that delegates to the <code>createXXX</code> methods.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected DbcmodelSwitch<Adapter> modelSwitch =
      new DbcmodelSwitch<Adapter>() {
         @Override
         public Adapter caseDbcModel(DbcModel object) {
            return createDbcModelAdapter();
         }
         @Override
         public Adapter caseDbcPackage(DbcPackage object) {
            return createDbcPackageAdapter();
         }
         @Override
         public Adapter caseDbcClass(DbcClass object) {
            return createDbcClassAdapter();
         }
         @Override
         public Adapter caseAbstractDbcProofContainer(AbstractDbcProofContainer object) {
            return createAbstractDbcProofContainerAdapter();
         }
         @Override
         public Adapter caseDbcMethod(DbcMethod object) {
            return createDbcMethodAdapter();
         }
         @Override
         public Adapter caseDbcInvariant(DbcInvariant object) {
            return createDbcInvariantAdapter();
         }
         @Override
         public Adapter caseDbcProof(DbcProof object) {
            return createDbcProofAdapter();
         }
         @Override
         public Adapter caseDbcConstructor(DbcConstructor object) {
            return createDbcConstructorAdapter();
         }
         @Override
         public Adapter caseDbcProofReference(DbcProofReference object) {
            return createDbcProofReferenceAdapter();
         }
         @Override
         public Adapter caseDbcAttribute(DbcAttribute object) {
            return createDbcAttributeAdapter();
         }
         @Override
         public Adapter caseAbstractDbcClass(AbstractDbcClass object) {
            return createAbstractDbcClassAdapter();
         }
         @Override
         public Adapter caseAbstractDbcInterface(AbstractDbcInterface object) {
            return createAbstractDbcInterfaceAdapter();
         }
         @Override
         public Adapter caseDbcInterface(DbcInterface object) {
            return createDbcInterfaceAdapter();
         }
         @Override
         public Adapter caseAbstractDbcType(AbstractDbcType object) {
            return createAbstractDbcTypeAdapter();
         }
         @Override
         public Adapter caseAbstractDbcEnum(AbstractDbcEnum object) {
            return createAbstractDbcEnumAdapter();
         }
         @Override
         public Adapter caseDbcEnum(DbcEnum object) {
            return createDbcEnumAdapter();
         }
         @Override
         public Adapter caseDbcEnumLiteral(DbcEnumLiteral object) {
            return createDbcEnumLiteralAdapter();
         }
         @Override
         public Adapter caseDbcOperationContract(DbcOperationContract object) {
            return createDbcOperationContractAdapter();
         }
         @Override
         public Adapter caseAbstractDbcSpecification(AbstractDbcSpecification object) {
            return createAbstractDbcSpecificationAdapter();
         }
         @Override
         public Adapter caseDbcProperty(DbcProperty object) {
            return createDbcPropertyAdapter();
         }
         @Override
         public Adapter caseAbstractDbcOperation(AbstractDbcOperation object) {
            return createAbstractDbcOperationAdapter();
         }
         @Override
         public Adapter caseAbstractDbCContainer(AbstractDbCContainer object) {
            return createAbstractDbCContainerAdapter();
         }
         @Override
         public Adapter caseAbstractDbcTypeContainer(AbstractDbcTypeContainer object) {
            return createAbstractDbcTypeContainerAdapter();
         }
         @Override
         public Adapter caseIDbCProvable(IDbCProvable object) {
            return createIDbCProvableAdapter();
         }
         @Override
         public Adapter caseIDbCProofReferencable(IDbCProofReferencable object) {
            return createIDbCProofReferencableAdapter();
         }
         @Override
         public Adapter caseDbcProofObligation(DbcProofObligation object) {
            return createDbcProofObligationAdapter();
         }
         @Override
         public Adapter caseDbcAxiom(DbcAxiom object) {
            return createDbcAxiomAdapter();
         }
         @Override
         public Adapter caseDbCAxiomContract(DbCAxiomContract object) {
            return createDbCAxiomContractAdapter();
         }
         @Override
         public Adapter defaultCase(EObject object) {
            return createEObjectAdapter();
         }
      };

   /**
    * Creates an adapter for the <code>target</code>.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param target the object to adapt.
    * @return the adapter for the <code>target</code>.
    * @generated
    */
   @Override
   public Adapter createAdapter(Notifier target) {
      return modelSwitch.doSwitch((EObject)target);
   }


   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.DbcModel <em>Dbc Model</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.DbcModel
    * @generated
    */
   public Adapter createDbcModelAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.DbcPackage <em>Dbc Package</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.DbcPackage
    * @generated
    */
   public Adapter createDbcPackageAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.DbcClass <em>Dbc Class</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.DbcClass
    * @generated
    */
   public Adapter createDbcClassAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcProofContainer <em>Abstract Dbc Proof Container</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcProofContainer
    * @generated
    */
   public Adapter createAbstractDbcProofContainerAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.DbcMethod <em>Dbc Method</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.DbcMethod
    * @generated
    */
   public Adapter createDbcMethodAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.DbcInvariant <em>Dbc Invariant</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.DbcInvariant
    * @generated
    */
   public Adapter createDbcInvariantAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.DbcProof <em>Dbc Proof</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.DbcProof
    * @generated
    */
   public Adapter createDbcProofAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.DbcConstructor <em>Dbc Constructor</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.DbcConstructor
    * @generated
    */
   public Adapter createDbcConstructorAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.DbcProofReference <em>Dbc Proof Reference</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.DbcProofReference
    * @generated
    */
   public Adapter createDbcProofReferenceAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.DbcAttribute <em>Dbc Attribute</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.DbcAttribute
    * @generated
    */
   public Adapter createDbcAttributeAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcClass <em>Abstract Dbc Class</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcClass
    * @generated
    */
   public Adapter createAbstractDbcClassAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcInterface <em>Abstract Dbc Interface</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcInterface
    * @generated
    */
   public Adapter createAbstractDbcInterfaceAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.DbcInterface <em>Dbc Interface</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.DbcInterface
    * @generated
    */
   public Adapter createDbcInterfaceAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcType <em>Abstract Dbc Type</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcType
    * @generated
    */
   public Adapter createAbstractDbcTypeAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcEnum <em>Abstract Dbc Enum</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcEnum
    * @generated
    */
   public Adapter createAbstractDbcEnumAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.DbcEnum <em>Dbc Enum</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.DbcEnum
    * @generated
    */
   public Adapter createDbcEnumAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.DbcEnumLiteral <em>Dbc Enum Literal</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.DbcEnumLiteral
    * @generated
    */
   public Adapter createDbcEnumLiteralAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.DbcOperationContract <em>Dbc Operation Contract</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.DbcOperationContract
    * @generated
    */
   public Adapter createDbcOperationContractAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcSpecification <em>Abstract Dbc Specification</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcSpecification
    * @generated
    */
   public Adapter createAbstractDbcSpecificationAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.DbcProperty <em>Dbc Property</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.DbcProperty
    * @generated
    */
   public Adapter createDbcPropertyAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation <em>Abstract Dbc Operation</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation
    * @generated
    */
   public Adapter createAbstractDbcOperationAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbCContainer <em>Abstract Db CContainer</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbCContainer
    * @generated
    */
   public Adapter createAbstractDbCContainerAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcTypeContainer <em>Abstract Dbc Type Container</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcTypeContainer
    * @generated
    */
   public Adapter createAbstractDbcTypeContainerAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.IDbCProvable <em>IDb CProvable</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.IDbCProvable
    * @generated
    */
   public Adapter createIDbCProvableAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable <em>IDb CProof Referencable</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable
    * @generated
    */
   public Adapter createIDbCProofReferencableAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.DbcProofObligation <em>Dbc Proof Obligation</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.DbcProofObligation
    * @generated
    */
   public Adapter createDbcProofObligationAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.DbcAxiom <em>Dbc Axiom</em>}'.
    * <!-- begin-user-doc -->
     * This default implementation returns null so that we can easily ignore cases;
     * it's useful to ignore a case when inheritance will catch all the cases anyway.
     * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.DbcAxiom
    * @generated
    */
    public Adapter createDbcAxiomAdapter() {
      return null;
   }

/**
    * Creates a new adapter for an object of class '{@link de.hentschel.visualdbc.dbcmodel.DbCAxiomContract <em>Db CAxiom Contract</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see de.hentschel.visualdbc.dbcmodel.DbCAxiomContract
    * @generated
    */
   public Adapter createDbCAxiomContractAdapter() {
      return null;
   }

/**
    * Creates a new adapter for the default case.
    * <!-- begin-user-doc -->
    * This default implementation returns null.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @generated
    */
   public Adapter createEObjectAdapter() {
      return null;
   }

} //DbcmodelAdapterFactory