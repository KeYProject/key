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
package de.hentschel.visualdbc.dbcmodel;

import org.eclipse.emf.ecore.EFactory;

/**
 * <!-- begin-user-doc -->
 * The <b>Factory</b> for the model.
 * It provides a create method for each non-abstract class of the model.
 * <!-- end-user-doc -->
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelPackage
 * @generated
 */
public interface DbcmodelFactory extends EFactory {
   /**
    * The singleton instance of the factory.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   DbcmodelFactory eINSTANCE = de.hentschel.visualdbc.dbcmodel.impl.DbcmodelFactoryImpl.init();

   /**
    * Returns a new object of class '<em>Dbc Model</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Dbc Model</em>'.
    * @generated
    */
   DbcModel createDbcModel();

   /**
    * Returns a new object of class '<em>Dbc Package</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Dbc Package</em>'.
    * @generated
    */
   DbcPackage createDbcPackage();

   /**
    * Returns a new object of class '<em>Dbc Class</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Dbc Class</em>'.
    * @generated
    */
   DbcClass createDbcClass();

   /**
    * Returns a new object of class '<em>Dbc Method</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Dbc Method</em>'.
    * @generated
    */
   DbcMethod createDbcMethod();

   /**
    * Returns a new object of class '<em>Dbc Invariant</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Dbc Invariant</em>'.
    * @generated
    */
   DbcInvariant createDbcInvariant();

   /**
    * Returns a new object of class '<em>Dbc Proof</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Dbc Proof</em>'.
    * @generated
    */
   DbcProof createDbcProof();

   /**
    * Returns a new object of class '<em>Dbc Constructor</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Dbc Constructor</em>'.
    * @generated
    */
   DbcConstructor createDbcConstructor();

   /**
    * Returns a new object of class '<em>Dbc Proof Reference</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Dbc Proof Reference</em>'.
    * @generated
    */
   DbcProofReference createDbcProofReference();

   /**
    * Returns a new object of class '<em>Dbc Attribute</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Dbc Attribute</em>'.
    * @generated
    */
   DbcAttribute createDbcAttribute();

   /**
    * Returns a new object of class '<em>Dbc Interface</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Dbc Interface</em>'.
    * @generated
    */
   DbcInterface createDbcInterface();

   /**
    * Returns a new object of class '<em>Dbc Enum</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Dbc Enum</em>'.
    * @generated
    */
   DbcEnum createDbcEnum();

   /**
    * Returns a new object of class '<em>Dbc Enum Literal</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Dbc Enum Literal</em>'.
    * @generated
    */
   DbcEnumLiteral createDbcEnumLiteral();

   /**
    * Returns a new object of class '<em>Dbc Operation Contract</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Dbc Operation Contract</em>'.
    * @generated
    */
   DbcOperationContract createDbcOperationContract();

   /**
    * Returns a new object of class '<em>Dbc Property</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Dbc Property</em>'.
    * @generated
    */
   DbcProperty createDbcProperty();

   /**
    * Returns a new object of class '<em>Dbc Proof Obligation</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Dbc Proof Obligation</em>'.
    * @generated
    */
   DbcProofObligation createDbcProofObligation();

   /**
    * Returns a new object of class '<em>Dbc Axiom</em>'.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @return a new object of class '<em>Dbc Axiom</em>'.
    * @generated
    */
    DbcAxiom createDbcAxiom();

/**
    * Returns a new object of class '<em>Db CAxiom Contract</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Db CAxiom Contract</em>'.
    * @generated
    */
   DbCAxiomContract createDbCAxiomContract();

/**
    * Returns the package supported by this factory.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the package supported by this factory.
    * @generated
    */
   DbcmodelPackage getDbcmodelPackage();

} //DbcmodelFactory