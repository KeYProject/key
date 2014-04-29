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
package de.hentschel.visualdbc.dbcmodel;

import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EDataType;
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
 *   <li>each enum,</li>
 *   <li>and each data type</li>
 * </ul>
 * <!-- end-user-doc -->
 * @see de.hentschel.visualdbc.dbcmodel.DbcmodelFactory
 * @model kind="package"
 * @generated
 */
public interface DbcmodelPackage extends EPackage {
   /**
    * The package name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   String eNAME = "dbcmodel";

   /**
    * The package namespace URI.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   String eNS_URI = "http://www.hentschel.de/dbcmodel";

   /**
    * The package namespace name.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   String eNS_PREFIX = "dbcmodel";

   /**
    * The singleton instance of the package.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   DbcmodelPackage eINSTANCE = de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl.init();

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcProofContainerImpl <em>Abstract Dbc Proof Container</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcProofContainerImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getAbstractDbcProofContainer()
    * @generated
    */
   int ABSTRACT_DBC_PROOF_CONTAINER = 3;

   /**
    * The feature id for the '<em><b>Proofs</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_PROOF_CONTAINER__PROOFS = 0;

   /**
    * The number of structural features of the '<em>Abstract Dbc Proof Container</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_PROOF_CONTAINER_FEATURE_COUNT = 1;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcTypeContainerImpl <em>Abstract Dbc Type Container</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcTypeContainerImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getAbstractDbcTypeContainer()
    * @generated
    */
   int ABSTRACT_DBC_TYPE_CONTAINER = 22;

   /**
    * The feature id for the '<em><b>Proofs</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_TYPE_CONTAINER__PROOFS = ABSTRACT_DBC_PROOF_CONTAINER__PROOFS;

   /**
    * The feature id for the '<em><b>Types</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_TYPE_CONTAINER__TYPES = ABSTRACT_DBC_PROOF_CONTAINER_FEATURE_COUNT + 0;

   /**
    * The number of structural features of the '<em>Abstract Dbc Type Container</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_TYPE_CONTAINER_FEATURE_COUNT = ABSTRACT_DBC_PROOF_CONTAINER_FEATURE_COUNT + 1;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbCContainerImpl <em>Abstract Db CContainer</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.AbstractDbCContainerImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getAbstractDbCContainer()
    * @generated
    */
   int ABSTRACT_DB_CCONTAINER = 21;

   /**
    * The feature id for the '<em><b>Proofs</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DB_CCONTAINER__PROOFS = ABSTRACT_DBC_TYPE_CONTAINER__PROOFS;

   /**
    * The feature id for the '<em><b>Types</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DB_CCONTAINER__TYPES = ABSTRACT_DBC_TYPE_CONTAINER__TYPES;

   /**
    * The feature id for the '<em><b>Packages</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DB_CCONTAINER__PACKAGES = ABSTRACT_DBC_TYPE_CONTAINER_FEATURE_COUNT + 0;

   /**
    * The number of structural features of the '<em>Abstract Db CContainer</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DB_CCONTAINER_FEATURE_COUNT = ABSTRACT_DBC_TYPE_CONTAINER_FEATURE_COUNT + 1;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcModelImpl <em>Dbc Model</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcModelImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcModel()
    * @generated
    */
   int DBC_MODEL = 0;

   /**
    * The feature id for the '<em><b>Proofs</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_MODEL__PROOFS = ABSTRACT_DB_CCONTAINER__PROOFS;

   /**
    * The feature id for the '<em><b>Types</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_MODEL__TYPES = ABSTRACT_DB_CCONTAINER__TYPES;

   /**
    * The feature id for the '<em><b>Packages</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_MODEL__PACKAGES = ABSTRACT_DB_CCONTAINER__PACKAGES;

   /**
    * The feature id for the '<em><b>Driver Id</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_MODEL__DRIVER_ID = ABSTRACT_DB_CCONTAINER_FEATURE_COUNT + 0;

   /**
    * The feature id for the '<em><b>Connection Settings</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_MODEL__CONNECTION_SETTINGS = ABSTRACT_DB_CCONTAINER_FEATURE_COUNT + 1;

   /**
    * The feature id for the '<em><b>Proof Obligations</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_MODEL__PROOF_OBLIGATIONS = ABSTRACT_DB_CCONTAINER_FEATURE_COUNT + 2;

   /**
    * The number of structural features of the '<em>Dbc Model</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_MODEL_FEATURE_COUNT = ABSTRACT_DB_CCONTAINER_FEATURE_COUNT + 3;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcPackageImpl <em>Dbc Package</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcPackageImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcPackage()
    * @generated
    */
   int DBC_PACKAGE = 1;

   /**
    * The feature id for the '<em><b>Proofs</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_PACKAGE__PROOFS = ABSTRACT_DB_CCONTAINER__PROOFS;

   /**
    * The feature id for the '<em><b>Types</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_PACKAGE__TYPES = ABSTRACT_DB_CCONTAINER__TYPES;

   /**
    * The feature id for the '<em><b>Packages</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_PACKAGE__PACKAGES = ABSTRACT_DB_CCONTAINER__PACKAGES;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_PACKAGE__NAME = ABSTRACT_DB_CCONTAINER_FEATURE_COUNT + 0;

   /**
    * The number of structural features of the '<em>Dbc Package</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_PACKAGE_FEATURE_COUNT = ABSTRACT_DB_CCONTAINER_FEATURE_COUNT + 1;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcTypeImpl <em>Abstract Dbc Type</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcTypeImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getAbstractDbcType()
    * @generated
    */
   int ABSTRACT_DBC_TYPE = 13;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcInterfaceImpl <em>Abstract Dbc Interface</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcInterfaceImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getAbstractDbcInterface()
    * @generated
    */
   int ABSTRACT_DBC_INTERFACE = 11;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcClassImpl <em>Abstract Dbc Class</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcClassImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getAbstractDbcClass()
    * @generated
    */
   int ABSTRACT_DBC_CLASS = 10;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcClassImpl <em>Dbc Class</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcClassImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcClass()
    * @generated
    */
   int DBC_CLASS = 2;

   /**
    * The feature id for the '<em><b>Proofs</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_TYPE__PROOFS = ABSTRACT_DBC_TYPE_CONTAINER__PROOFS;

   /**
    * The feature id for the '<em><b>Types</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_TYPE__TYPES = ABSTRACT_DBC_TYPE_CONTAINER__TYPES;

   /**
    * The feature id for the '<em><b>All References</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_TYPE__ALL_REFERENCES = ABSTRACT_DBC_TYPE_CONTAINER_FEATURE_COUNT + 0;

   /**
    * The feature id for the '<em><b>Proof Obligations</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_TYPE__PROOF_OBLIGATIONS = ABSTRACT_DBC_TYPE_CONTAINER_FEATURE_COUNT + 1;

   /**
    * The feature id for the '<em><b>All Proofs</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_TYPE__ALL_PROOFS = ABSTRACT_DBC_TYPE_CONTAINER_FEATURE_COUNT + 2;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_TYPE__NAME = ABSTRACT_DBC_TYPE_CONTAINER_FEATURE_COUNT + 3;

   /**
    * The feature id for the '<em><b>Visibility</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_TYPE__VISIBILITY = ABSTRACT_DBC_TYPE_CONTAINER_FEATURE_COUNT + 4;

   /**
    * The feature id for the '<em><b>Static</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_TYPE__STATIC = ABSTRACT_DBC_TYPE_CONTAINER_FEATURE_COUNT + 5;

   /**
    * The feature id for the '<em><b>Invariants</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_TYPE__INVARIANTS = ABSTRACT_DBC_TYPE_CONTAINER_FEATURE_COUNT + 6;

   /**
    * The feature id for the '<em><b>Axioms</b></em>' containment reference list.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
    int ABSTRACT_DBC_TYPE__AXIOMS = ABSTRACT_DBC_TYPE_CONTAINER_FEATURE_COUNT + 7;

/**
    * The number of structural features of the '<em>Abstract Dbc Type</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_TYPE_FEATURE_COUNT = ABSTRACT_DBC_TYPE_CONTAINER_FEATURE_COUNT + 8;

   /**
    * The feature id for the '<em><b>Proofs</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_INTERFACE__PROOFS = ABSTRACT_DBC_TYPE__PROOFS;

   /**
    * The feature id for the '<em><b>Types</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_INTERFACE__TYPES = ABSTRACT_DBC_TYPE__TYPES;

   /**
    * The feature id for the '<em><b>All References</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_INTERFACE__ALL_REFERENCES = ABSTRACT_DBC_TYPE__ALL_REFERENCES;

   /**
    * The feature id for the '<em><b>Proof Obligations</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_INTERFACE__PROOF_OBLIGATIONS = ABSTRACT_DBC_TYPE__PROOF_OBLIGATIONS;

   /**
    * The feature id for the '<em><b>All Proofs</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_INTERFACE__ALL_PROOFS = ABSTRACT_DBC_TYPE__ALL_PROOFS;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_INTERFACE__NAME = ABSTRACT_DBC_TYPE__NAME;

   /**
    * The feature id for the '<em><b>Visibility</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_INTERFACE__VISIBILITY = ABSTRACT_DBC_TYPE__VISIBILITY;

   /**
    * The feature id for the '<em><b>Static</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_INTERFACE__STATIC = ABSTRACT_DBC_TYPE__STATIC;

   /**
    * The feature id for the '<em><b>Invariants</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_INTERFACE__INVARIANTS = ABSTRACT_DBC_TYPE__INVARIANTS;

   /**
    * The feature id for the '<em><b>Axioms</b></em>' containment reference list.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
    int ABSTRACT_DBC_INTERFACE__AXIOMS = ABSTRACT_DBC_TYPE__AXIOMS;

/**
    * The feature id for the '<em><b>Methods</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_INTERFACE__METHODS = ABSTRACT_DBC_TYPE_FEATURE_COUNT + 0;

   /**
    * The feature id for the '<em><b>Attributes</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_INTERFACE__ATTRIBUTES = ABSTRACT_DBC_TYPE_FEATURE_COUNT + 1;

   /**
    * The number of structural features of the '<em>Abstract Dbc Interface</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_INTERFACE_FEATURE_COUNT = ABSTRACT_DBC_TYPE_FEATURE_COUNT + 2;

   /**
    * The feature id for the '<em><b>Proofs</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_CLASS__PROOFS = ABSTRACT_DBC_INTERFACE__PROOFS;

   /**
    * The feature id for the '<em><b>Types</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_CLASS__TYPES = ABSTRACT_DBC_INTERFACE__TYPES;

   /**
    * The feature id for the '<em><b>All References</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_CLASS__ALL_REFERENCES = ABSTRACT_DBC_INTERFACE__ALL_REFERENCES;

   /**
    * The feature id for the '<em><b>Proof Obligations</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_CLASS__PROOF_OBLIGATIONS = ABSTRACT_DBC_INTERFACE__PROOF_OBLIGATIONS;

   /**
    * The feature id for the '<em><b>All Proofs</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_CLASS__ALL_PROOFS = ABSTRACT_DBC_INTERFACE__ALL_PROOFS;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_CLASS__NAME = ABSTRACT_DBC_INTERFACE__NAME;

   /**
    * The feature id for the '<em><b>Visibility</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_CLASS__VISIBILITY = ABSTRACT_DBC_INTERFACE__VISIBILITY;

   /**
    * The feature id for the '<em><b>Static</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_CLASS__STATIC = ABSTRACT_DBC_INTERFACE__STATIC;

   /**
    * The feature id for the '<em><b>Invariants</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_CLASS__INVARIANTS = ABSTRACT_DBC_INTERFACE__INVARIANTS;

   /**
    * The feature id for the '<em><b>Axioms</b></em>' containment reference list.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
    int ABSTRACT_DBC_CLASS__AXIOMS = ABSTRACT_DBC_INTERFACE__AXIOMS;

/**
    * The feature id for the '<em><b>Methods</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_CLASS__METHODS = ABSTRACT_DBC_INTERFACE__METHODS;

   /**
    * The feature id for the '<em><b>Attributes</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_CLASS__ATTRIBUTES = ABSTRACT_DBC_INTERFACE__ATTRIBUTES;

   /**
    * The feature id for the '<em><b>Constructors</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_CLASS__CONSTRUCTORS = ABSTRACT_DBC_INTERFACE_FEATURE_COUNT + 0;

   /**
    * The feature id for the '<em><b>Implements</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_CLASS__IMPLEMENTS = ABSTRACT_DBC_INTERFACE_FEATURE_COUNT + 1;

   /**
    * The feature id for the '<em><b>Implements Full Names</b></em>' attribute list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_CLASS__IMPLEMENTS_FULL_NAMES = ABSTRACT_DBC_INTERFACE_FEATURE_COUNT + 2;

   /**
    * The number of structural features of the '<em>Abstract Dbc Class</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_CLASS_FEATURE_COUNT = ABSTRACT_DBC_INTERFACE_FEATURE_COUNT + 3;

   /**
    * The feature id for the '<em><b>Proofs</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CLASS__PROOFS = ABSTRACT_DBC_CLASS__PROOFS;

   /**
    * The feature id for the '<em><b>Types</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CLASS__TYPES = ABSTRACT_DBC_CLASS__TYPES;

   /**
    * The feature id for the '<em><b>All References</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CLASS__ALL_REFERENCES = ABSTRACT_DBC_CLASS__ALL_REFERENCES;

   /**
    * The feature id for the '<em><b>Proof Obligations</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CLASS__PROOF_OBLIGATIONS = ABSTRACT_DBC_CLASS__PROOF_OBLIGATIONS;

   /**
    * The feature id for the '<em><b>All Proofs</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CLASS__ALL_PROOFS = ABSTRACT_DBC_CLASS__ALL_PROOFS;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CLASS__NAME = ABSTRACT_DBC_CLASS__NAME;

   /**
    * The feature id for the '<em><b>Visibility</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CLASS__VISIBILITY = ABSTRACT_DBC_CLASS__VISIBILITY;

   /**
    * The feature id for the '<em><b>Static</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CLASS__STATIC = ABSTRACT_DBC_CLASS__STATIC;

   /**
    * The feature id for the '<em><b>Invariants</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CLASS__INVARIANTS = ABSTRACT_DBC_CLASS__INVARIANTS;

   /**
    * The feature id for the '<em><b>Axioms</b></em>' containment reference list.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
    int DBC_CLASS__AXIOMS = ABSTRACT_DBC_CLASS__AXIOMS;

/**
    * The feature id for the '<em><b>Methods</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CLASS__METHODS = ABSTRACT_DBC_CLASS__METHODS;

   /**
    * The feature id for the '<em><b>Attributes</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CLASS__ATTRIBUTES = ABSTRACT_DBC_CLASS__ATTRIBUTES;

   /**
    * The feature id for the '<em><b>Constructors</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CLASS__CONSTRUCTORS = ABSTRACT_DBC_CLASS__CONSTRUCTORS;

   /**
    * The feature id for the '<em><b>Implements</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CLASS__IMPLEMENTS = ABSTRACT_DBC_CLASS__IMPLEMENTS;

   /**
    * The feature id for the '<em><b>Implements Full Names</b></em>' attribute list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CLASS__IMPLEMENTS_FULL_NAMES = ABSTRACT_DBC_CLASS__IMPLEMENTS_FULL_NAMES;

   /**
    * The feature id for the '<em><b>Abstract</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CLASS__ABSTRACT = ABSTRACT_DBC_CLASS_FEATURE_COUNT + 0;

   /**
    * The feature id for the '<em><b>Final</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CLASS__FINAL = ABSTRACT_DBC_CLASS_FEATURE_COUNT + 1;

   /**
    * The feature id for the '<em><b>Extends</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CLASS__EXTENDS = ABSTRACT_DBC_CLASS_FEATURE_COUNT + 2;

   /**
    * The feature id for the '<em><b>Anonymous</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CLASS__ANONYMOUS = ABSTRACT_DBC_CLASS_FEATURE_COUNT + 3;

   /**
    * The feature id for the '<em><b>Extends Full Names</b></em>' attribute list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CLASS__EXTENDS_FULL_NAMES = ABSTRACT_DBC_CLASS_FEATURE_COUNT + 4;

   /**
    * The number of structural features of the '<em>Dbc Class</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CLASS_FEATURE_COUNT = ABSTRACT_DBC_CLASS_FEATURE_COUNT + 5;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcMethodImpl <em>Dbc Method</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcMethodImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcMethod()
    * @generated
    */
   int DBC_METHOD = 4;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcSpecificationImpl <em>Abstract Dbc Specification</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcSpecificationImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getAbstractDbcSpecification()
    * @generated
    */
   int ABSTRACT_DBC_SPECIFICATION = 18;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcInvariantImpl <em>Dbc Invariant</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcInvariantImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcInvariant()
    * @generated
    */
   int DBC_INVARIANT = 5;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcProofImpl <em>Dbc Proof</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcProofImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcProof()
    * @generated
    */
   int DBC_PROOF = 6;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcConstructorImpl <em>Dbc Constructor</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcConstructorImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcConstructor()
    * @generated
    */
   int DBC_CONSTRUCTOR = 7;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcProofReferenceImpl <em>Dbc Proof Reference</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcProofReferenceImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcProofReference()
    * @generated
    */
   int DBC_PROOF_REFERENCE = 8;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcAttributeImpl <em>Dbc Attribute</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcAttributeImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcAttribute()
    * @generated
    */
   int DBC_ATTRIBUTE = 9;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcInterfaceImpl <em>Dbc Interface</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcInterfaceImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcInterface()
    * @generated
    */
   int DBC_INTERFACE = 12;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcEnumImpl <em>Abstract Dbc Enum</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcEnumImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getAbstractDbcEnum()
    * @generated
    */
   int ABSTRACT_DBC_ENUM = 14;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcEnumImpl <em>Dbc Enum</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcEnumImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcEnum()
    * @generated
    */
   int DBC_ENUM = 15;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcEnumLiteralImpl <em>Dbc Enum Literal</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcEnumLiteralImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcEnumLiteral()
    * @generated
    */
   int DBC_ENUM_LITERAL = 16;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcOperationContractImpl <em>Dbc Operation Contract</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcOperationContractImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcOperationContract()
    * @generated
    */
   int DBC_OPERATION_CONTRACT = 17;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcPropertyImpl <em>Dbc Property</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcPropertyImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcProperty()
    * @generated
    */
   int DBC_PROPERTY = 19;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcOperationImpl <em>Abstract Dbc Operation</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcOperationImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getAbstractDbcOperation()
    * @generated
    */
   int ABSTRACT_DBC_OPERATION = 20;

   /**
    * The feature id for the '<em><b>Proofs</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_OPERATION__PROOFS = ABSTRACT_DBC_PROOF_CONTAINER__PROOFS;

   /**
    * The feature id for the '<em><b>All References</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_OPERATION__ALL_REFERENCES = ABSTRACT_DBC_PROOF_CONTAINER_FEATURE_COUNT + 0;

   /**
    * The feature id for the '<em><b>Proof Obligations</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_OPERATION__PROOF_OBLIGATIONS = ABSTRACT_DBC_PROOF_CONTAINER_FEATURE_COUNT + 1;

   /**
    * The feature id for the '<em><b>All Proofs</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_OPERATION__ALL_PROOFS = ABSTRACT_DBC_PROOF_CONTAINER_FEATURE_COUNT + 2;

   /**
    * The feature id for the '<em><b>Operation Contracts</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_OPERATION__OPERATION_CONTRACTS = ABSTRACT_DBC_PROOF_CONTAINER_FEATURE_COUNT + 3;

   /**
    * The feature id for the '<em><b>Signature</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_OPERATION__SIGNATURE = ABSTRACT_DBC_PROOF_CONTAINER_FEATURE_COUNT + 4;

   /**
    * The feature id for the '<em><b>Visibility</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_OPERATION__VISIBILITY = ABSTRACT_DBC_PROOF_CONTAINER_FEATURE_COUNT + 5;

   /**
    * The feature id for the '<em><b>Static</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_OPERATION__STATIC = ABSTRACT_DBC_PROOF_CONTAINER_FEATURE_COUNT + 6;

   /**
    * The number of structural features of the '<em>Abstract Dbc Operation</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_OPERATION_FEATURE_COUNT = ABSTRACT_DBC_PROOF_CONTAINER_FEATURE_COUNT + 7;

   /**
    * The feature id for the '<em><b>Proofs</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_METHOD__PROOFS = ABSTRACT_DBC_OPERATION__PROOFS;

   /**
    * The feature id for the '<em><b>All References</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_METHOD__ALL_REFERENCES = ABSTRACT_DBC_OPERATION__ALL_REFERENCES;

   /**
    * The feature id for the '<em><b>Proof Obligations</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_METHOD__PROOF_OBLIGATIONS = ABSTRACT_DBC_OPERATION__PROOF_OBLIGATIONS;

   /**
    * The feature id for the '<em><b>All Proofs</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_METHOD__ALL_PROOFS = ABSTRACT_DBC_OPERATION__ALL_PROOFS;

   /**
    * The feature id for the '<em><b>Operation Contracts</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_METHOD__OPERATION_CONTRACTS = ABSTRACT_DBC_OPERATION__OPERATION_CONTRACTS;

   /**
    * The feature id for the '<em><b>Signature</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_METHOD__SIGNATURE = ABSTRACT_DBC_OPERATION__SIGNATURE;

   /**
    * The feature id for the '<em><b>Visibility</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_METHOD__VISIBILITY = ABSTRACT_DBC_OPERATION__VISIBILITY;

   /**
    * The feature id for the '<em><b>Static</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_METHOD__STATIC = ABSTRACT_DBC_OPERATION__STATIC;

   /**
    * The feature id for the '<em><b>Return Type</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_METHOD__RETURN_TYPE = ABSTRACT_DBC_OPERATION_FEATURE_COUNT + 0;

   /**
    * The feature id for the '<em><b>Abstract</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_METHOD__ABSTRACT = ABSTRACT_DBC_OPERATION_FEATURE_COUNT + 1;

   /**
    * The feature id for the '<em><b>Final</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_METHOD__FINAL = ABSTRACT_DBC_OPERATION_FEATURE_COUNT + 2;

   /**
    * The number of structural features of the '<em>Dbc Method</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_METHOD_FEATURE_COUNT = ABSTRACT_DBC_OPERATION_FEATURE_COUNT + 3;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_SPECIFICATION__NAME = 0;

   /**
    * The number of structural features of the '<em>Abstract Dbc Specification</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_SPECIFICATION_FEATURE_COUNT = 1;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_INVARIANT__NAME = ABSTRACT_DBC_SPECIFICATION__NAME;

   /**
    * The feature id for the '<em><b>All References</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_INVARIANT__ALL_REFERENCES = ABSTRACT_DBC_SPECIFICATION_FEATURE_COUNT + 0;

   /**
    * The feature id for the '<em><b>Condition</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_INVARIANT__CONDITION = ABSTRACT_DBC_SPECIFICATION_FEATURE_COUNT + 1;

   /**
    * The number of structural features of the '<em>Dbc Invariant</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_INVARIANT_FEATURE_COUNT = ABSTRACT_DBC_SPECIFICATION_FEATURE_COUNT + 2;

   /**
    * The feature id for the '<em><b>Target</b></em>' reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_PROOF__TARGET = 0;

   /**
    * The feature id for the '<em><b>Proof References</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_PROOF__PROOF_REFERENCES = 1;

   /**
    * The feature id for the '<em><b>Obligation</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_PROOF__OBLIGATION = 2;

   /**
    * The feature id for the '<em><b>Status</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_PROOF__STATUS = 3;

   /**
    * The number of structural features of the '<em>Dbc Proof</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_PROOF_FEATURE_COUNT = 4;

   /**
    * The feature id for the '<em><b>Proofs</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CONSTRUCTOR__PROOFS = ABSTRACT_DBC_OPERATION__PROOFS;

   /**
    * The feature id for the '<em><b>All References</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CONSTRUCTOR__ALL_REFERENCES = ABSTRACT_DBC_OPERATION__ALL_REFERENCES;

   /**
    * The feature id for the '<em><b>Proof Obligations</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CONSTRUCTOR__PROOF_OBLIGATIONS = ABSTRACT_DBC_OPERATION__PROOF_OBLIGATIONS;

   /**
    * The feature id for the '<em><b>All Proofs</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CONSTRUCTOR__ALL_PROOFS = ABSTRACT_DBC_OPERATION__ALL_PROOFS;

   /**
    * The feature id for the '<em><b>Operation Contracts</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CONSTRUCTOR__OPERATION_CONTRACTS = ABSTRACT_DBC_OPERATION__OPERATION_CONTRACTS;

   /**
    * The feature id for the '<em><b>Signature</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CONSTRUCTOR__SIGNATURE = ABSTRACT_DBC_OPERATION__SIGNATURE;

   /**
    * The feature id for the '<em><b>Visibility</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CONSTRUCTOR__VISIBILITY = ABSTRACT_DBC_OPERATION__VISIBILITY;

   /**
    * The feature id for the '<em><b>Static</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CONSTRUCTOR__STATIC = ABSTRACT_DBC_OPERATION__STATIC;

   /**
    * The number of structural features of the '<em>Dbc Constructor</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_CONSTRUCTOR_FEATURE_COUNT = ABSTRACT_DBC_OPERATION_FEATURE_COUNT + 0;

   /**
    * The feature id for the '<em><b>Target</b></em>' reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_PROOF_REFERENCE__TARGET = 0;

   /**
    * The feature id for the '<em><b>Kind</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_PROOF_REFERENCE__KIND = 1;

   /**
    * The feature id for the '<em><b>Source</b></em>' reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_PROOF_REFERENCE__SOURCE = 2;

   /**
    * The number of structural features of the '<em>Dbc Proof Reference</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_PROOF_REFERENCE_FEATURE_COUNT = 3;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable <em>IDb CProof Referencable</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getIDbCProofReferencable()
    * @generated
    */
   int IDB_CPROOF_REFERENCABLE = 24;

   /**
    * The feature id for the '<em><b>All References</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int IDB_CPROOF_REFERENCABLE__ALL_REFERENCES = 0;

   /**
    * The number of structural features of the '<em>IDb CProof Referencable</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int IDB_CPROOF_REFERENCABLE_FEATURE_COUNT = 1;

   /**
    * The feature id for the '<em><b>All References</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ATTRIBUTE__ALL_REFERENCES = IDB_CPROOF_REFERENCABLE__ALL_REFERENCES;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ATTRIBUTE__NAME = IDB_CPROOF_REFERENCABLE_FEATURE_COUNT + 0;

   /**
    * The feature id for the '<em><b>Type</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ATTRIBUTE__TYPE = IDB_CPROOF_REFERENCABLE_FEATURE_COUNT + 1;

   /**
    * The feature id for the '<em><b>Visibility</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ATTRIBUTE__VISIBILITY = IDB_CPROOF_REFERENCABLE_FEATURE_COUNT + 2;

   /**
    * The feature id for the '<em><b>Static</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ATTRIBUTE__STATIC = IDB_CPROOF_REFERENCABLE_FEATURE_COUNT + 3;

   /**
    * The feature id for the '<em><b>Final</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ATTRIBUTE__FINAL = IDB_CPROOF_REFERENCABLE_FEATURE_COUNT + 4;

   /**
    * The number of structural features of the '<em>Dbc Attribute</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ATTRIBUTE_FEATURE_COUNT = IDB_CPROOF_REFERENCABLE_FEATURE_COUNT + 5;

   /**
    * The feature id for the '<em><b>Proofs</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_INTERFACE__PROOFS = ABSTRACT_DBC_INTERFACE__PROOFS;

   /**
    * The feature id for the '<em><b>Types</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_INTERFACE__TYPES = ABSTRACT_DBC_INTERFACE__TYPES;

   /**
    * The feature id for the '<em><b>All References</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_INTERFACE__ALL_REFERENCES = ABSTRACT_DBC_INTERFACE__ALL_REFERENCES;

   /**
    * The feature id for the '<em><b>Proof Obligations</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_INTERFACE__PROOF_OBLIGATIONS = ABSTRACT_DBC_INTERFACE__PROOF_OBLIGATIONS;

   /**
    * The feature id for the '<em><b>All Proofs</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_INTERFACE__ALL_PROOFS = ABSTRACT_DBC_INTERFACE__ALL_PROOFS;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_INTERFACE__NAME = ABSTRACT_DBC_INTERFACE__NAME;

   /**
    * The feature id for the '<em><b>Visibility</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_INTERFACE__VISIBILITY = ABSTRACT_DBC_INTERFACE__VISIBILITY;

   /**
    * The feature id for the '<em><b>Static</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_INTERFACE__STATIC = ABSTRACT_DBC_INTERFACE__STATIC;

   /**
    * The feature id for the '<em><b>Invariants</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_INTERFACE__INVARIANTS = ABSTRACT_DBC_INTERFACE__INVARIANTS;

   /**
    * The feature id for the '<em><b>Axioms</b></em>' containment reference list.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
    int DBC_INTERFACE__AXIOMS = ABSTRACT_DBC_INTERFACE__AXIOMS;

   /**
    * The feature id for the '<em><b>Methods</b></em>' containment reference list.
    * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
      int DBC_INTERFACE__METHODS = ABSTRACT_DBC_INTERFACE__METHODS;

   /**
    * The feature id for the '<em><b>Attributes</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_INTERFACE__ATTRIBUTES = ABSTRACT_DBC_INTERFACE__ATTRIBUTES;

   /**
    * The feature id for the '<em><b>Extends</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_INTERFACE__EXTENDS = ABSTRACT_DBC_INTERFACE_FEATURE_COUNT + 0;

   /**
    * The feature id for the '<em><b>Extends Full Names</b></em>' attribute list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_INTERFACE__EXTENDS_FULL_NAMES = ABSTRACT_DBC_INTERFACE_FEATURE_COUNT + 1;

   /**
    * The number of structural features of the '<em>Dbc Interface</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_INTERFACE_FEATURE_COUNT = ABSTRACT_DBC_INTERFACE_FEATURE_COUNT + 2;

   /**
    * The feature id for the '<em><b>Proofs</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_ENUM__PROOFS = ABSTRACT_DBC_CLASS__PROOFS;

   /**
    * The feature id for the '<em><b>Types</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_ENUM__TYPES = ABSTRACT_DBC_CLASS__TYPES;

   /**
    * The feature id for the '<em><b>All References</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_ENUM__ALL_REFERENCES = ABSTRACT_DBC_CLASS__ALL_REFERENCES;

   /**
    * The feature id for the '<em><b>Proof Obligations</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_ENUM__PROOF_OBLIGATIONS = ABSTRACT_DBC_CLASS__PROOF_OBLIGATIONS;

   /**
    * The feature id for the '<em><b>All Proofs</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_ENUM__ALL_PROOFS = ABSTRACT_DBC_CLASS__ALL_PROOFS;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_ENUM__NAME = ABSTRACT_DBC_CLASS__NAME;

   /**
    * The feature id for the '<em><b>Visibility</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_ENUM__VISIBILITY = ABSTRACT_DBC_CLASS__VISIBILITY;

   /**
    * The feature id for the '<em><b>Static</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_ENUM__STATIC = ABSTRACT_DBC_CLASS__STATIC;

   /**
    * The feature id for the '<em><b>Invariants</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_ENUM__INVARIANTS = ABSTRACT_DBC_CLASS__INVARIANTS;

   /**
    * The feature id for the '<em><b>Axioms</b></em>' containment reference list.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
    int ABSTRACT_DBC_ENUM__AXIOMS = ABSTRACT_DBC_CLASS__AXIOMS;

   /**
    * The feature id for the '<em><b>Methods</b></em>' containment reference list.
    * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
      int ABSTRACT_DBC_ENUM__METHODS = ABSTRACT_DBC_CLASS__METHODS;

   /**
    * The feature id for the '<em><b>Attributes</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_ENUM__ATTRIBUTES = ABSTRACT_DBC_CLASS__ATTRIBUTES;

   /**
    * The feature id for the '<em><b>Constructors</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_ENUM__CONSTRUCTORS = ABSTRACT_DBC_CLASS__CONSTRUCTORS;

   /**
    * The feature id for the '<em><b>Implements</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_ENUM__IMPLEMENTS = ABSTRACT_DBC_CLASS__IMPLEMENTS;

   /**
    * The feature id for the '<em><b>Implements Full Names</b></em>' attribute list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_ENUM__IMPLEMENTS_FULL_NAMES = ABSTRACT_DBC_CLASS__IMPLEMENTS_FULL_NAMES;

   /**
    * The feature id for the '<em><b>Literals</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_ENUM__LITERALS = ABSTRACT_DBC_CLASS_FEATURE_COUNT + 0;

   /**
    * The number of structural features of the '<em>Abstract Dbc Enum</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int ABSTRACT_DBC_ENUM_FEATURE_COUNT = ABSTRACT_DBC_CLASS_FEATURE_COUNT + 1;

   /**
    * The feature id for the '<em><b>Proofs</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ENUM__PROOFS = ABSTRACT_DBC_ENUM__PROOFS;

   /**
    * The feature id for the '<em><b>Types</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ENUM__TYPES = ABSTRACT_DBC_ENUM__TYPES;

   /**
    * The feature id for the '<em><b>All References</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ENUM__ALL_REFERENCES = ABSTRACT_DBC_ENUM__ALL_REFERENCES;

   /**
    * The feature id for the '<em><b>Proof Obligations</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ENUM__PROOF_OBLIGATIONS = ABSTRACT_DBC_ENUM__PROOF_OBLIGATIONS;

   /**
    * The feature id for the '<em><b>All Proofs</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ENUM__ALL_PROOFS = ABSTRACT_DBC_ENUM__ALL_PROOFS;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ENUM__NAME = ABSTRACT_DBC_ENUM__NAME;

   /**
    * The feature id for the '<em><b>Visibility</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ENUM__VISIBILITY = ABSTRACT_DBC_ENUM__VISIBILITY;

   /**
    * The feature id for the '<em><b>Static</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ENUM__STATIC = ABSTRACT_DBC_ENUM__STATIC;

   /**
    * The feature id for the '<em><b>Invariants</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ENUM__INVARIANTS = ABSTRACT_DBC_ENUM__INVARIANTS;

   /**
    * The feature id for the '<em><b>Axioms</b></em>' containment reference list.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
    int DBC_ENUM__AXIOMS = ABSTRACT_DBC_ENUM__AXIOMS;

   /**
    * The feature id for the '<em><b>Methods</b></em>' containment reference list.
    * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
      int DBC_ENUM__METHODS = ABSTRACT_DBC_ENUM__METHODS;

   /**
    * The feature id for the '<em><b>Attributes</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ENUM__ATTRIBUTES = ABSTRACT_DBC_ENUM__ATTRIBUTES;

   /**
    * The feature id for the '<em><b>Constructors</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ENUM__CONSTRUCTORS = ABSTRACT_DBC_ENUM__CONSTRUCTORS;

   /**
    * The feature id for the '<em><b>Implements</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ENUM__IMPLEMENTS = ABSTRACT_DBC_ENUM__IMPLEMENTS;

   /**
    * The feature id for the '<em><b>Implements Full Names</b></em>' attribute list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ENUM__IMPLEMENTS_FULL_NAMES = ABSTRACT_DBC_ENUM__IMPLEMENTS_FULL_NAMES;

   /**
    * The feature id for the '<em><b>Literals</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ENUM__LITERALS = ABSTRACT_DBC_ENUM__LITERALS;

   /**
    * The number of structural features of the '<em>Dbc Enum</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ENUM_FEATURE_COUNT = ABSTRACT_DBC_ENUM_FEATURE_COUNT + 0;

   /**
    * The feature id for the '<em><b>All References</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ENUM_LITERAL__ALL_REFERENCES = IDB_CPROOF_REFERENCABLE__ALL_REFERENCES;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ENUM_LITERAL__NAME = IDB_CPROOF_REFERENCABLE_FEATURE_COUNT + 0;

   /**
    * The number of structural features of the '<em>Dbc Enum Literal</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_ENUM_LITERAL_FEATURE_COUNT = IDB_CPROOF_REFERENCABLE_FEATURE_COUNT + 1;

   /**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_OPERATION_CONTRACT__NAME = ABSTRACT_DBC_SPECIFICATION__NAME;

   /**
    * The feature id for the '<em><b>All References</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_OPERATION_CONTRACT__ALL_REFERENCES = ABSTRACT_DBC_SPECIFICATION_FEATURE_COUNT + 0;

   /**
    * The feature id for the '<em><b>Proof Obligations</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_OPERATION_CONTRACT__PROOF_OBLIGATIONS = ABSTRACT_DBC_SPECIFICATION_FEATURE_COUNT + 1;

   /**
    * The feature id for the '<em><b>All Proofs</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_OPERATION_CONTRACT__ALL_PROOFS = ABSTRACT_DBC_SPECIFICATION_FEATURE_COUNT + 2;

   /**
    * The feature id for the '<em><b>Pre</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_OPERATION_CONTRACT__PRE = ABSTRACT_DBC_SPECIFICATION_FEATURE_COUNT + 3;

   /**
    * The feature id for the '<em><b>Post</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_OPERATION_CONTRACT__POST = ABSTRACT_DBC_SPECIFICATION_FEATURE_COUNT + 4;

   /**
    * The feature id for the '<em><b>Modifies</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_OPERATION_CONTRACT__MODIFIES = ABSTRACT_DBC_SPECIFICATION_FEATURE_COUNT + 5;

   /**
    * The feature id for the '<em><b>Termination</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_OPERATION_CONTRACT__TERMINATION = ABSTRACT_DBC_SPECIFICATION_FEATURE_COUNT + 6;

   /**
    * The number of structural features of the '<em>Dbc Operation Contract</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_OPERATION_CONTRACT_FEATURE_COUNT = ABSTRACT_DBC_SPECIFICATION_FEATURE_COUNT + 7;

   /**
    * The feature id for the '<em><b>Key</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_PROPERTY__KEY = 0;

   /**
    * The feature id for the '<em><b>Value</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_PROPERTY__VALUE = 1;

   /**
    * The number of structural features of the '<em>Dbc Property</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_PROPERTY_FEATURE_COUNT = 2;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.IDbCProvable <em>IDb CProvable</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.IDbCProvable
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getIDbCProvable()
    * @generated
    */
   int IDB_CPROVABLE = 23;

   /**
    * The feature id for the '<em><b>All References</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int IDB_CPROVABLE__ALL_REFERENCES = IDB_CPROOF_REFERENCABLE__ALL_REFERENCES;

   /**
    * The feature id for the '<em><b>Proof Obligations</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int IDB_CPROVABLE__PROOF_OBLIGATIONS = IDB_CPROOF_REFERENCABLE_FEATURE_COUNT + 0;

   /**
    * The feature id for the '<em><b>All Proofs</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int IDB_CPROVABLE__ALL_PROOFS = IDB_CPROOF_REFERENCABLE_FEATURE_COUNT + 1;

   /**
    * The number of structural features of the '<em>IDb CProvable</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int IDB_CPROVABLE_FEATURE_COUNT = IDB_CPROOF_REFERENCABLE_FEATURE_COUNT + 2;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcProofObligationImpl <em>Dbc Proof Obligation</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcProofObligationImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcProofObligation()
    * @generated
    */
   int DBC_PROOF_OBLIGATION = 25;

   /**
    * The feature id for the '<em><b>Obligation</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_PROOF_OBLIGATION__OBLIGATION = 0;

   /**
    * The number of structural features of the '<em>Dbc Proof Obligation</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_PROOF_OBLIGATION_FEATURE_COUNT = 1;

   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcAxiomImpl <em>Dbc Axiom</em>}' class.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcAxiomImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcAxiom()
    * @generated
    */
    int DBC_AXIOM = 26;

/**
    * The feature id for the '<em><b>All References</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_AXIOM__ALL_REFERENCES = IDB_CPROOF_REFERENCABLE__ALL_REFERENCES;

/**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
    int DBC_AXIOM__NAME = IDB_CPROOF_REFERENCABLE_FEATURE_COUNT + 0;

/**
    * The feature id for the '<em><b>Definition</b></em>' attribute.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
    int DBC_AXIOM__DEFINITION = IDB_CPROOF_REFERENCABLE_FEATURE_COUNT + 1;

/**
    * The feature id for the '<em><b>Axiom Contracts</b></em>' containment reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DBC_AXIOM__AXIOM_CONTRACTS = IDB_CPROOF_REFERENCABLE_FEATURE_COUNT + 2;

/**
    * The number of structural features of the '<em>Dbc Axiom</em>' class.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
    int DBC_AXIOM_FEATURE_COUNT = IDB_CPROOF_REFERENCABLE_FEATURE_COUNT + 3;

/**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbCAxiomContractImpl <em>Db CAxiom Contract</em>}' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbCAxiomContractImpl
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbCAxiomContract()
    * @generated
    */
   int DB_CAXIOM_CONTRACT = 27;

/**
    * The feature id for the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DB_CAXIOM_CONTRACT__NAME = ABSTRACT_DBC_SPECIFICATION__NAME;

/**
    * The feature id for the '<em><b>All References</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DB_CAXIOM_CONTRACT__ALL_REFERENCES = ABSTRACT_DBC_SPECIFICATION_FEATURE_COUNT + 0;

/**
    * The feature id for the '<em><b>Proof Obligations</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DB_CAXIOM_CONTRACT__PROOF_OBLIGATIONS = ABSTRACT_DBC_SPECIFICATION_FEATURE_COUNT + 1;

/**
    * The feature id for the '<em><b>All Proofs</b></em>' reference list.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DB_CAXIOM_CONTRACT__ALL_PROOFS = ABSTRACT_DBC_SPECIFICATION_FEATURE_COUNT + 2;

/**
    * The feature id for the '<em><b>Pre</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DB_CAXIOM_CONTRACT__PRE = ABSTRACT_DBC_SPECIFICATION_FEATURE_COUNT + 3;

/**
    * The feature id for the '<em><b>Dep</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DB_CAXIOM_CONTRACT__DEP = ABSTRACT_DBC_SPECIFICATION_FEATURE_COUNT + 4;

/**
    * The number of structural features of the '<em>Db CAxiom Contract</em>' class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    * @ordered
    */
   int DB_CAXIOM_CONTRACT_FEATURE_COUNT = ABSTRACT_DBC_SPECIFICATION_FEATURE_COUNT + 5;

/**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.DbcVisibility <em>Dbc Visibility</em>}' enum.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.DbcVisibility
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcVisibility()
    * @generated
    */
   int DBC_VISIBILITY = 28;


   /**
    * The meta object id for the '{@link de.hentschel.visualdbc.dbcmodel.DbcProofStatus <em>Dbc Proof Status</em>}' enum.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see de.hentschel.visualdbc.dbcmodel.DbcProofStatus
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcProofStatus()
    * @generated
    */
   int DBC_PROOF_STATUS = 29;


   /**
    * The meta object id for the '<em>Properties</em>' data type.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @see java.util.Properties
    * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getProperties()
    * @generated
    */
   int PROPERTIES = 30;

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.DbcModel <em>Dbc Model</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Dbc Model</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcModel
    * @generated
    */
   EClass getDbcModel();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcModel#getDriverId <em>Driver Id</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Driver Id</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcModel#getDriverId()
    * @see #getDbcModel()
    * @generated
    */
   EAttribute getDbcModel_DriverId();

   /**
    * Returns the meta object for the containment reference list '{@link de.hentschel.visualdbc.dbcmodel.DbcModel#getConnectionSettings <em>Connection Settings</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Connection Settings</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcModel#getConnectionSettings()
    * @see #getDbcModel()
    * @generated
    */
   EReference getDbcModel_ConnectionSettings();

   /**
    * Returns the meta object for the containment reference list '{@link de.hentschel.visualdbc.dbcmodel.DbcModel#getProofObligations <em>Proof Obligations</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Proof Obligations</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcModel#getProofObligations()
    * @see #getDbcModel()
    * @generated
    */
   EReference getDbcModel_ProofObligations();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.DbcPackage <em>Dbc Package</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Dbc Package</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcPackage
    * @generated
    */
   EClass getDbcPackage();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcPackage#getName <em>Name</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Name</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcPackage#getName()
    * @see #getDbcPackage()
    * @generated
    */
   EAttribute getDbcPackage_Name();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.DbcClass <em>Dbc Class</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Dbc Class</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcClass
    * @generated
    */
   EClass getDbcClass();

   /**
    * Returns the meta object for the reference list '{@link de.hentschel.visualdbc.dbcmodel.DbcClass#getExtends <em>Extends</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the reference list '<em>Extends</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcClass#getExtends()
    * @see #getDbcClass()
    * @generated
    */
   EReference getDbcClass_Extends();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcClass#isAnonymous <em>Anonymous</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Anonymous</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcClass#isAnonymous()
    * @see #getDbcClass()
    * @generated
    */
   EAttribute getDbcClass_Anonymous();

   /**
    * Returns the meta object for the attribute list '{@link de.hentschel.visualdbc.dbcmodel.DbcClass#getExtendsFullNames <em>Extends Full Names</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute list '<em>Extends Full Names</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcClass#getExtendsFullNames()
    * @see #getDbcClass()
    * @generated
    */
   EAttribute getDbcClass_ExtendsFullNames();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcProofContainer <em>Abstract Dbc Proof Container</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Abstract Dbc Proof Container</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcProofContainer
    * @generated
    */
   EClass getAbstractDbcProofContainer();

   /**
    * Returns the meta object for the containment reference list '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcProofContainer#getProofs <em>Proofs</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Proofs</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcProofContainer#getProofs()
    * @see #getAbstractDbcProofContainer()
    * @generated
    */
   EReference getAbstractDbcProofContainer_Proofs();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcClass#isAbstract <em>Abstract</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Abstract</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcClass#isAbstract()
    * @see #getDbcClass()
    * @generated
    */
   EAttribute getDbcClass_Abstract();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcClass#isFinal <em>Final</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Final</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcClass#isFinal()
    * @see #getDbcClass()
    * @generated
    */
   EAttribute getDbcClass_Final();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.DbcMethod <em>Dbc Method</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Dbc Method</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcMethod
    * @generated
    */
   EClass getDbcMethod();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcMethod#getReturnType <em>Return Type</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Return Type</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcMethod#getReturnType()
    * @see #getDbcMethod()
    * @generated
    */
   EAttribute getDbcMethod_ReturnType();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcMethod#isAbstract <em>Abstract</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Abstract</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcMethod#isAbstract()
    * @see #getDbcMethod()
    * @generated
    */
   EAttribute getDbcMethod_Abstract();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcMethod#isFinal <em>Final</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Final</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcMethod#isFinal()
    * @see #getDbcMethod()
    * @generated
    */
   EAttribute getDbcMethod_Final();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.DbcInvariant <em>Dbc Invariant</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Dbc Invariant</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcInvariant
    * @generated
    */
   EClass getDbcInvariant();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcInvariant#getCondition <em>Condition</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Condition</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcInvariant#getCondition()
    * @see #getDbcInvariant()
    * @generated
    */
   EAttribute getDbcInvariant_Condition();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.DbcProof <em>Dbc Proof</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Dbc Proof</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcProof
    * @generated
    */
   EClass getDbcProof();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcProof#getObligation <em>Obligation</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Obligation</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcProof#getObligation()
    * @see #getDbcProof()
    * @generated
    */
   EAttribute getDbcProof_Obligation();

   /**
    * Returns the meta object for the reference '{@link de.hentschel.visualdbc.dbcmodel.DbcProof#getTarget <em>Target</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the reference '<em>Target</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcProof#getTarget()
    * @see #getDbcProof()
    * @generated
    */
   EReference getDbcProof_Target();

   /**
    * Returns the meta object for the containment reference list '{@link de.hentschel.visualdbc.dbcmodel.DbcProof#getProofReferences <em>Proof References</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Proof References</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcProof#getProofReferences()
    * @see #getDbcProof()
    * @generated
    */
   EReference getDbcProof_ProofReferences();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcProof#getStatus <em>Status</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Status</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcProof#getStatus()
    * @see #getDbcProof()
    * @generated
    */
   EAttribute getDbcProof_Status();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.DbcConstructor <em>Dbc Constructor</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Dbc Constructor</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcConstructor
    * @generated
    */
   EClass getDbcConstructor();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.DbcProofReference <em>Dbc Proof Reference</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Dbc Proof Reference</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcProofReference
    * @generated
    */
   EClass getDbcProofReference();

   /**
    * Returns the meta object for the reference '{@link de.hentschel.visualdbc.dbcmodel.DbcProofReference#getTarget <em>Target</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the reference '<em>Target</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcProofReference#getTarget()
    * @see #getDbcProofReference()
    * @generated
    */
   EReference getDbcProofReference_Target();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcProofReference#getKind <em>Kind</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Kind</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcProofReference#getKind()
    * @see #getDbcProofReference()
    * @generated
    */
   EAttribute getDbcProofReference_Kind();

   /**
    * Returns the meta object for the reference '{@link de.hentschel.visualdbc.dbcmodel.DbcProofReference#getSource <em>Source</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the reference '<em>Source</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcProofReference#getSource()
    * @see #getDbcProofReference()
    * @generated
    */
   EReference getDbcProofReference_Source();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.DbcAttribute <em>Dbc Attribute</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Dbc Attribute</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcAttribute
    * @generated
    */
   EClass getDbcAttribute();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcAttribute#getName <em>Name</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Name</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcAttribute#getName()
    * @see #getDbcAttribute()
    * @generated
    */
   EAttribute getDbcAttribute_Name();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcAttribute#getType <em>Type</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Type</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcAttribute#getType()
    * @see #getDbcAttribute()
    * @generated
    */
   EAttribute getDbcAttribute_Type();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcAttribute#getVisibility <em>Visibility</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Visibility</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcAttribute#getVisibility()
    * @see #getDbcAttribute()
    * @generated
    */
   EAttribute getDbcAttribute_Visibility();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcAttribute#isStatic <em>Static</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Static</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcAttribute#isStatic()
    * @see #getDbcAttribute()
    * @generated
    */
   EAttribute getDbcAttribute_Static();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcAttribute#isFinal <em>Final</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Final</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcAttribute#isFinal()
    * @see #getDbcAttribute()
    * @generated
    */
   EAttribute getDbcAttribute_Final();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcClass <em>Abstract Dbc Class</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Abstract Dbc Class</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcClass
    * @generated
    */
   EClass getAbstractDbcClass();

   /**
    * Returns the meta object for the containment reference list '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcClass#getConstructors <em>Constructors</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Constructors</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcClass#getConstructors()
    * @see #getAbstractDbcClass()
    * @generated
    */
   EReference getAbstractDbcClass_Constructors();

   /**
    * Returns the meta object for the reference list '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcClass#getImplements <em>Implements</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the reference list '<em>Implements</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcClass#getImplements()
    * @see #getAbstractDbcClass()
    * @generated
    */
   EReference getAbstractDbcClass_Implements();

   /**
    * Returns the meta object for the attribute list '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcClass#getImplementsFullNames <em>Implements Full Names</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute list '<em>Implements Full Names</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcClass#getImplementsFullNames()
    * @see #getAbstractDbcClass()
    * @generated
    */
   EAttribute getAbstractDbcClass_ImplementsFullNames();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcInterface <em>Abstract Dbc Interface</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Abstract Dbc Interface</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcInterface
    * @generated
    */
   EClass getAbstractDbcInterface();

   /**
    * Returns the meta object for the containment reference list '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcInterface#getMethods <em>Methods</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Methods</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcInterface#getMethods()
    * @see #getAbstractDbcInterface()
    * @generated
    */
   EReference getAbstractDbcInterface_Methods();

   /**
    * Returns the meta object for the containment reference list '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcInterface#getAttributes <em>Attributes</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Attributes</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcInterface#getAttributes()
    * @see #getAbstractDbcInterface()
    * @generated
    */
   EReference getAbstractDbcInterface_Attributes();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.DbcInterface <em>Dbc Interface</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Dbc Interface</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcInterface
    * @generated
    */
   EClass getDbcInterface();

   /**
    * Returns the meta object for the reference list '{@link de.hentschel.visualdbc.dbcmodel.DbcInterface#getExtends <em>Extends</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the reference list '<em>Extends</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcInterface#getExtends()
    * @see #getDbcInterface()
    * @generated
    */
   EReference getDbcInterface_Extends();

   /**
    * Returns the meta object for the attribute list '{@link de.hentschel.visualdbc.dbcmodel.DbcInterface#getExtendsFullNames <em>Extends Full Names</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute list '<em>Extends Full Names</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcInterface#getExtendsFullNames()
    * @see #getDbcInterface()
    * @generated
    */
   EAttribute getDbcInterface_ExtendsFullNames();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcType <em>Abstract Dbc Type</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Abstract Dbc Type</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcType
    * @generated
    */
   EClass getAbstractDbcType();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcType#getName <em>Name</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Name</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcType#getName()
    * @see #getAbstractDbcType()
    * @generated
    */
   EAttribute getAbstractDbcType_Name();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcType#getVisibility <em>Visibility</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Visibility</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcType#getVisibility()
    * @see #getAbstractDbcType()
    * @generated
    */
   EAttribute getAbstractDbcType_Visibility();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcType#isStatic <em>Static</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Static</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcType#isStatic()
    * @see #getAbstractDbcType()
    * @generated
    */
   EAttribute getAbstractDbcType_Static();

   /**
    * Returns the meta object for the containment reference list '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcType#getInvariants <em>Invariants</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Invariants</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcType#getInvariants()
    * @see #getAbstractDbcType()
    * @generated
    */
   EReference getAbstractDbcType_Invariants();

   /**
    * Returns the meta object for the containment reference list '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcType#getAxioms <em>Axioms</em>}'.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Axioms</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcType#getAxioms()
    * @see #getAbstractDbcType()
    * @generated
    */
    EReference getAbstractDbcType_Axioms();

/**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcEnum <em>Abstract Dbc Enum</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Abstract Dbc Enum</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcEnum
    * @generated
    */
   EClass getAbstractDbcEnum();

   /**
    * Returns the meta object for the containment reference list '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcEnum#getLiterals <em>Literals</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Literals</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcEnum#getLiterals()
    * @see #getAbstractDbcEnum()
    * @generated
    */
   EReference getAbstractDbcEnum_Literals();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.DbcEnum <em>Dbc Enum</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Dbc Enum</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcEnum
    * @generated
    */
   EClass getDbcEnum();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.DbcEnumLiteral <em>Dbc Enum Literal</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Dbc Enum Literal</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcEnumLiteral
    * @generated
    */
   EClass getDbcEnumLiteral();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcEnumLiteral#getName <em>Name</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Name</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcEnumLiteral#getName()
    * @see #getDbcEnumLiteral()
    * @generated
    */
   EAttribute getDbcEnumLiteral_Name();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.DbcOperationContract <em>Dbc Operation Contract</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Dbc Operation Contract</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcOperationContract
    * @generated
    */
   EClass getDbcOperationContract();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcOperationContract#getPre <em>Pre</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Pre</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcOperationContract#getPre()
    * @see #getDbcOperationContract()
    * @generated
    */
   EAttribute getDbcOperationContract_Pre();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcOperationContract#getPost <em>Post</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Post</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcOperationContract#getPost()
    * @see #getDbcOperationContract()
    * @generated
    */
   EAttribute getDbcOperationContract_Post();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcOperationContract#getModifies <em>Modifies</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Modifies</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcOperationContract#getModifies()
    * @see #getDbcOperationContract()
    * @generated
    */
   EAttribute getDbcOperationContract_Modifies();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcOperationContract#getTermination <em>Termination</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Termination</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcOperationContract#getTermination()
    * @see #getDbcOperationContract()
    * @generated
    */
   EAttribute getDbcOperationContract_Termination();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcSpecification <em>Abstract Dbc Specification</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Abstract Dbc Specification</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcSpecification
    * @generated
    */
   EClass getAbstractDbcSpecification();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcSpecification#getName <em>Name</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Name</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcSpecification#getName()
    * @see #getAbstractDbcSpecification()
    * @generated
    */
   EAttribute getAbstractDbcSpecification_Name();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.DbcProperty <em>Dbc Property</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Dbc Property</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcProperty
    * @generated
    */
   EClass getDbcProperty();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcProperty#getKey <em>Key</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Key</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcProperty#getKey()
    * @see #getDbcProperty()
    * @generated
    */
   EAttribute getDbcProperty_Key();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcProperty#getValue <em>Value</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Value</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcProperty#getValue()
    * @see #getDbcProperty()
    * @generated
    */
   EAttribute getDbcProperty_Value();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation <em>Abstract Dbc Operation</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Abstract Dbc Operation</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation
    * @generated
    */
   EClass getAbstractDbcOperation();

   /**
    * Returns the meta object for the containment reference list '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation#getOperationContracts <em>Operation Contracts</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Operation Contracts</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation#getOperationContracts()
    * @see #getAbstractDbcOperation()
    * @generated
    */
   EReference getAbstractDbcOperation_OperationContracts();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation#getSignature <em>Signature</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Signature</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation#getSignature()
    * @see #getAbstractDbcOperation()
    * @generated
    */
   EAttribute getAbstractDbcOperation_Signature();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation#getVisibility <em>Visibility</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Visibility</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation#getVisibility()
    * @see #getAbstractDbcOperation()
    * @generated
    */
   EAttribute getAbstractDbcOperation_Visibility();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation#isStatic <em>Static</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Static</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation#isStatic()
    * @see #getAbstractDbcOperation()
    * @generated
    */
   EAttribute getAbstractDbcOperation_Static();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbCContainer <em>Abstract Db CContainer</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Abstract Db CContainer</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbCContainer
    * @generated
    */
   EClass getAbstractDbCContainer();

   /**
    * Returns the meta object for the containment reference list '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbCContainer#getPackages <em>Packages</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Packages</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbCContainer#getPackages()
    * @see #getAbstractDbCContainer()
    * @generated
    */
   EReference getAbstractDbCContainer_Packages();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcTypeContainer <em>Abstract Dbc Type Container</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Abstract Dbc Type Container</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcTypeContainer
    * @generated
    */
   EClass getAbstractDbcTypeContainer();

   /**
    * Returns the meta object for the containment reference list '{@link de.hentschel.visualdbc.dbcmodel.AbstractDbcTypeContainer#getTypes <em>Types</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Types</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.AbstractDbcTypeContainer#getTypes()
    * @see #getAbstractDbcTypeContainer()
    * @generated
    */
   EReference getAbstractDbcTypeContainer_Types();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.IDbCProvable <em>IDb CProvable</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>IDb CProvable</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.IDbCProvable
    * @generated
    */
   EClass getIDbCProvable();

   /**
    * Returns the meta object for the reference list '{@link de.hentschel.visualdbc.dbcmodel.IDbCProvable#getProofObligations <em>Proof Obligations</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the reference list '<em>Proof Obligations</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.IDbCProvable#getProofObligations()
    * @see #getIDbCProvable()
    * @generated
    */
   EReference getIDbCProvable_ProofObligations();

   /**
    * Returns the meta object for the reference list '{@link de.hentschel.visualdbc.dbcmodel.IDbCProvable#getAllProofs <em>All Proofs</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the reference list '<em>All Proofs</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.IDbCProvable#getAllProofs()
    * @see #getIDbCProvable()
    * @generated
    */
   EReference getIDbCProvable_AllProofs();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable <em>IDb CProof Referencable</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>IDb CProof Referencable</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable
    * @generated
    */
   EClass getIDbCProofReferencable();

   /**
    * Returns the meta object for the reference list '{@link de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable#getAllReferences <em>All References</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the reference list '<em>All References</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable#getAllReferences()
    * @see #getIDbCProofReferencable()
    * @generated
    */
   EReference getIDbCProofReferencable_AllReferences();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.DbcProofObligation <em>Dbc Proof Obligation</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Dbc Proof Obligation</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcProofObligation
    * @generated
    */
   EClass getDbcProofObligation();

   /**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcProofObligation#getObligation <em>Obligation</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Obligation</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcProofObligation#getObligation()
    * @see #getDbcProofObligation()
    * @generated
    */
   EAttribute getDbcProofObligation_Obligation();

   /**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.DbcAxiom <em>Dbc Axiom</em>}'.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @return the meta object for class '<em>Dbc Axiom</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcAxiom
    * @generated
    */
    EClass getDbcAxiom();

/**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbcAxiom#getDefinition <em>Definition</em>}'.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Definition</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcAxiom#getDefinition()
    * @see #getDbcAxiom()
    * @generated
    */
    EAttribute getDbcAxiom_Definition();

/**
    * Returns the meta object for the containment reference list '{@link de.hentschel.visualdbc.dbcmodel.DbcAxiom#getAxiomContracts <em>Axiom Contracts</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the containment reference list '<em>Axiom Contracts</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcAxiom#getAxiomContracts()
    * @see #getDbcAxiom()
    * @generated
    */
   EReference getDbcAxiom_AxiomContracts();

/**
    * Returns the meta object for class '{@link de.hentschel.visualdbc.dbcmodel.DbCAxiomContract <em>Db CAxiom Contract</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for class '<em>Db CAxiom Contract</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbCAxiomContract
    * @generated
    */
   EClass getDbCAxiomContract();

/**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbCAxiomContract#getPre <em>Pre</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Pre</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbCAxiomContract#getPre()
    * @see #getDbCAxiomContract()
    * @generated
    */
   EAttribute getDbCAxiomContract_Pre();

/**
    * Returns the meta object for the attribute '{@link de.hentschel.visualdbc.dbcmodel.DbCAxiomContract#getDep <em>Dep</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for the attribute '<em>Dep</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbCAxiomContract#getDep()
    * @see #getDbCAxiomContract()
    * @generated
    */
   EAttribute getDbCAxiomContract_Dep();

/**
    * Returns the meta object for enum '{@link de.hentschel.visualdbc.dbcmodel.DbcVisibility <em>Dbc Visibility</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for enum '<em>Dbc Visibility</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcVisibility
    * @generated
    */
   EEnum getDbcVisibility();

   /**
    * Returns the meta object for enum '{@link de.hentschel.visualdbc.dbcmodel.DbcProofStatus <em>Dbc Proof Status</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for enum '<em>Dbc Proof Status</em>'.
    * @see de.hentschel.visualdbc.dbcmodel.DbcProofStatus
    * @generated
    */
   EEnum getDbcProofStatus();

   /**
    * Returns the meta object for data type '{@link java.util.Properties <em>Properties</em>}'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the meta object for data type '<em>Properties</em>'.
    * @see java.util.Properties
    * @model instanceClass="java.util.Properties"
    * @generated
    */
   EDataType getProperties();

   /**
    * Returns the factory that creates the instances of the model.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the factory that creates the instances of the model.
    * @generated
    */
   DbcmodelFactory getDbcmodelFactory();

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
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcModelImpl <em>Dbc Model</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcModelImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcModel()
       * @generated
       */
      EClass DBC_MODEL = eINSTANCE.getDbcModel();

      /**
       * The meta object literal for the '<em><b>Driver Id</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_MODEL__DRIVER_ID = eINSTANCE.getDbcModel_DriverId();

      /**
       * The meta object literal for the '<em><b>Connection Settings</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference DBC_MODEL__CONNECTION_SETTINGS = eINSTANCE.getDbcModel_ConnectionSettings();

      /**
       * The meta object literal for the '<em><b>Proof Obligations</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference DBC_MODEL__PROOF_OBLIGATIONS = eINSTANCE.getDbcModel_ProofObligations();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcPackageImpl <em>Dbc Package</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcPackageImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcPackage()
       * @generated
       */
      EClass DBC_PACKAGE = eINSTANCE.getDbcPackage();

      /**
       * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_PACKAGE__NAME = eINSTANCE.getDbcPackage_Name();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcClassImpl <em>Dbc Class</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcClassImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcClass()
       * @generated
       */
      EClass DBC_CLASS = eINSTANCE.getDbcClass();

      /**
       * The meta object literal for the '<em><b>Extends</b></em>' reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference DBC_CLASS__EXTENDS = eINSTANCE.getDbcClass_Extends();

      /**
       * The meta object literal for the '<em><b>Anonymous</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_CLASS__ANONYMOUS = eINSTANCE.getDbcClass_Anonymous();

      /**
       * The meta object literal for the '<em><b>Extends Full Names</b></em>' attribute list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_CLASS__EXTENDS_FULL_NAMES = eINSTANCE.getDbcClass_ExtendsFullNames();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcProofContainerImpl <em>Abstract Dbc Proof Container</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcProofContainerImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getAbstractDbcProofContainer()
       * @generated
       */
      EClass ABSTRACT_DBC_PROOF_CONTAINER = eINSTANCE.getAbstractDbcProofContainer();

      /**
       * The meta object literal for the '<em><b>Proofs</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference ABSTRACT_DBC_PROOF_CONTAINER__PROOFS = eINSTANCE.getAbstractDbcProofContainer_Proofs();

      /**
       * The meta object literal for the '<em><b>Abstract</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_CLASS__ABSTRACT = eINSTANCE.getDbcClass_Abstract();

      /**
       * The meta object literal for the '<em><b>Final</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_CLASS__FINAL = eINSTANCE.getDbcClass_Final();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcMethodImpl <em>Dbc Method</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcMethodImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcMethod()
       * @generated
       */
      EClass DBC_METHOD = eINSTANCE.getDbcMethod();

      /**
       * The meta object literal for the '<em><b>Return Type</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_METHOD__RETURN_TYPE = eINSTANCE.getDbcMethod_ReturnType();

      /**
       * The meta object literal for the '<em><b>Abstract</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_METHOD__ABSTRACT = eINSTANCE.getDbcMethod_Abstract();

      /**
       * The meta object literal for the '<em><b>Final</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_METHOD__FINAL = eINSTANCE.getDbcMethod_Final();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcInvariantImpl <em>Dbc Invariant</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcInvariantImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcInvariant()
       * @generated
       */
      EClass DBC_INVARIANT = eINSTANCE.getDbcInvariant();

      /**
       * The meta object literal for the '<em><b>Condition</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_INVARIANT__CONDITION = eINSTANCE.getDbcInvariant_Condition();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcProofImpl <em>Dbc Proof</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcProofImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcProof()
       * @generated
       */
      EClass DBC_PROOF = eINSTANCE.getDbcProof();

      /**
       * The meta object literal for the '<em><b>Obligation</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_PROOF__OBLIGATION = eINSTANCE.getDbcProof_Obligation();

      /**
       * The meta object literal for the '<em><b>Target</b></em>' reference feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference DBC_PROOF__TARGET = eINSTANCE.getDbcProof_Target();

      /**
       * The meta object literal for the '<em><b>Proof References</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference DBC_PROOF__PROOF_REFERENCES = eINSTANCE.getDbcProof_ProofReferences();

      /**
       * The meta object literal for the '<em><b>Status</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_PROOF__STATUS = eINSTANCE.getDbcProof_Status();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcConstructorImpl <em>Dbc Constructor</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcConstructorImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcConstructor()
       * @generated
       */
      EClass DBC_CONSTRUCTOR = eINSTANCE.getDbcConstructor();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcProofReferenceImpl <em>Dbc Proof Reference</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcProofReferenceImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcProofReference()
       * @generated
       */
      EClass DBC_PROOF_REFERENCE = eINSTANCE.getDbcProofReference();

      /**
       * The meta object literal for the '<em><b>Target</b></em>' reference feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference DBC_PROOF_REFERENCE__TARGET = eINSTANCE.getDbcProofReference_Target();

      /**
       * The meta object literal for the '<em><b>Kind</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_PROOF_REFERENCE__KIND = eINSTANCE.getDbcProofReference_Kind();

      /**
       * The meta object literal for the '<em><b>Source</b></em>' reference feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference DBC_PROOF_REFERENCE__SOURCE = eINSTANCE.getDbcProofReference_Source();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcAttributeImpl <em>Dbc Attribute</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcAttributeImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcAttribute()
       * @generated
       */
      EClass DBC_ATTRIBUTE = eINSTANCE.getDbcAttribute();

      /**
       * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_ATTRIBUTE__NAME = eINSTANCE.getDbcAttribute_Name();

      /**
       * The meta object literal for the '<em><b>Type</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_ATTRIBUTE__TYPE = eINSTANCE.getDbcAttribute_Type();

      /**
       * The meta object literal for the '<em><b>Visibility</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_ATTRIBUTE__VISIBILITY = eINSTANCE.getDbcAttribute_Visibility();

      /**
       * The meta object literal for the '<em><b>Static</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_ATTRIBUTE__STATIC = eINSTANCE.getDbcAttribute_Static();

      /**
       * The meta object literal for the '<em><b>Final</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_ATTRIBUTE__FINAL = eINSTANCE.getDbcAttribute_Final();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcClassImpl <em>Abstract Dbc Class</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcClassImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getAbstractDbcClass()
       * @generated
       */
      EClass ABSTRACT_DBC_CLASS = eINSTANCE.getAbstractDbcClass();

      /**
       * The meta object literal for the '<em><b>Constructors</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference ABSTRACT_DBC_CLASS__CONSTRUCTORS = eINSTANCE.getAbstractDbcClass_Constructors();

      /**
       * The meta object literal for the '<em><b>Implements</b></em>' reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference ABSTRACT_DBC_CLASS__IMPLEMENTS = eINSTANCE.getAbstractDbcClass_Implements();

      /**
       * The meta object literal for the '<em><b>Implements Full Names</b></em>' attribute list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute ABSTRACT_DBC_CLASS__IMPLEMENTS_FULL_NAMES = eINSTANCE.getAbstractDbcClass_ImplementsFullNames();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcInterfaceImpl <em>Abstract Dbc Interface</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcInterfaceImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getAbstractDbcInterface()
       * @generated
       */
      EClass ABSTRACT_DBC_INTERFACE = eINSTANCE.getAbstractDbcInterface();

      /**
       * The meta object literal for the '<em><b>Methods</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference ABSTRACT_DBC_INTERFACE__METHODS = eINSTANCE.getAbstractDbcInterface_Methods();

      /**
       * The meta object literal for the '<em><b>Attributes</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference ABSTRACT_DBC_INTERFACE__ATTRIBUTES = eINSTANCE.getAbstractDbcInterface_Attributes();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcInterfaceImpl <em>Dbc Interface</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcInterfaceImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcInterface()
       * @generated
       */
      EClass DBC_INTERFACE = eINSTANCE.getDbcInterface();

      /**
       * The meta object literal for the '<em><b>Extends</b></em>' reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference DBC_INTERFACE__EXTENDS = eINSTANCE.getDbcInterface_Extends();

      /**
       * The meta object literal for the '<em><b>Extends Full Names</b></em>' attribute list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_INTERFACE__EXTENDS_FULL_NAMES = eINSTANCE.getDbcInterface_ExtendsFullNames();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcTypeImpl <em>Abstract Dbc Type</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcTypeImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getAbstractDbcType()
       * @generated
       */
      EClass ABSTRACT_DBC_TYPE = eINSTANCE.getAbstractDbcType();

      /**
       * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute ABSTRACT_DBC_TYPE__NAME = eINSTANCE.getAbstractDbcType_Name();

      /**
       * The meta object literal for the '<em><b>Visibility</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute ABSTRACT_DBC_TYPE__VISIBILITY = eINSTANCE.getAbstractDbcType_Visibility();

      /**
       * The meta object literal for the '<em><b>Static</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute ABSTRACT_DBC_TYPE__STATIC = eINSTANCE.getAbstractDbcType_Static();

      /**
       * The meta object literal for the '<em><b>Invariants</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference ABSTRACT_DBC_TYPE__INVARIANTS = eINSTANCE.getAbstractDbcType_Invariants();

      /**
       * The meta object literal for the '<em><b>Axioms</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
         * <!-- end-user-doc -->
       * @generated
       */
        EReference ABSTRACT_DBC_TYPE__AXIOMS = eINSTANCE.getAbstractDbcType_Axioms();

    /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcEnumImpl <em>Abstract Dbc Enum</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcEnumImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getAbstractDbcEnum()
       * @generated
       */
      EClass ABSTRACT_DBC_ENUM = eINSTANCE.getAbstractDbcEnum();

      /**
       * The meta object literal for the '<em><b>Literals</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference ABSTRACT_DBC_ENUM__LITERALS = eINSTANCE.getAbstractDbcEnum_Literals();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcEnumImpl <em>Dbc Enum</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcEnumImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcEnum()
       * @generated
       */
      EClass DBC_ENUM = eINSTANCE.getDbcEnum();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcEnumLiteralImpl <em>Dbc Enum Literal</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcEnumLiteralImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcEnumLiteral()
       * @generated
       */
      EClass DBC_ENUM_LITERAL = eINSTANCE.getDbcEnumLiteral();

      /**
       * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_ENUM_LITERAL__NAME = eINSTANCE.getDbcEnumLiteral_Name();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcOperationContractImpl <em>Dbc Operation Contract</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcOperationContractImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcOperationContract()
       * @generated
       */
      EClass DBC_OPERATION_CONTRACT = eINSTANCE.getDbcOperationContract();

      /**
       * The meta object literal for the '<em><b>Pre</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_OPERATION_CONTRACT__PRE = eINSTANCE.getDbcOperationContract_Pre();

      /**
       * The meta object literal for the '<em><b>Post</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_OPERATION_CONTRACT__POST = eINSTANCE.getDbcOperationContract_Post();

      /**
       * The meta object literal for the '<em><b>Modifies</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_OPERATION_CONTRACT__MODIFIES = eINSTANCE.getDbcOperationContract_Modifies();

      /**
       * The meta object literal for the '<em><b>Termination</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_OPERATION_CONTRACT__TERMINATION = eINSTANCE.getDbcOperationContract_Termination();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcSpecificationImpl <em>Abstract Dbc Specification</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcSpecificationImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getAbstractDbcSpecification()
       * @generated
       */
      EClass ABSTRACT_DBC_SPECIFICATION = eINSTANCE.getAbstractDbcSpecification();

      /**
       * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute ABSTRACT_DBC_SPECIFICATION__NAME = eINSTANCE.getAbstractDbcSpecification_Name();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcPropertyImpl <em>Dbc Property</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcPropertyImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcProperty()
       * @generated
       */
      EClass DBC_PROPERTY = eINSTANCE.getDbcProperty();

      /**
       * The meta object literal for the '<em><b>Key</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_PROPERTY__KEY = eINSTANCE.getDbcProperty_Key();

      /**
       * The meta object literal for the '<em><b>Value</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_PROPERTY__VALUE = eINSTANCE.getDbcProperty_Value();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcOperationImpl <em>Abstract Dbc Operation</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcOperationImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getAbstractDbcOperation()
       * @generated
       */
      EClass ABSTRACT_DBC_OPERATION = eINSTANCE.getAbstractDbcOperation();

      /**
       * The meta object literal for the '<em><b>Operation Contracts</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference ABSTRACT_DBC_OPERATION__OPERATION_CONTRACTS = eINSTANCE.getAbstractDbcOperation_OperationContracts();

      /**
       * The meta object literal for the '<em><b>Signature</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute ABSTRACT_DBC_OPERATION__SIGNATURE = eINSTANCE.getAbstractDbcOperation_Signature();

      /**
       * The meta object literal for the '<em><b>Visibility</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute ABSTRACT_DBC_OPERATION__VISIBILITY = eINSTANCE.getAbstractDbcOperation_Visibility();

      /**
       * The meta object literal for the '<em><b>Static</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute ABSTRACT_DBC_OPERATION__STATIC = eINSTANCE.getAbstractDbcOperation_Static();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbCContainerImpl <em>Abstract Db CContainer</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.AbstractDbCContainerImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getAbstractDbCContainer()
       * @generated
       */
      EClass ABSTRACT_DB_CCONTAINER = eINSTANCE.getAbstractDbCContainer();

      /**
       * The meta object literal for the '<em><b>Packages</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference ABSTRACT_DB_CCONTAINER__PACKAGES = eINSTANCE.getAbstractDbCContainer_Packages();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcTypeContainerImpl <em>Abstract Dbc Type Container</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.AbstractDbcTypeContainerImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getAbstractDbcTypeContainer()
       * @generated
       */
      EClass ABSTRACT_DBC_TYPE_CONTAINER = eINSTANCE.getAbstractDbcTypeContainer();

      /**
       * The meta object literal for the '<em><b>Types</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference ABSTRACT_DBC_TYPE_CONTAINER__TYPES = eINSTANCE.getAbstractDbcTypeContainer_Types();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.IDbCProvable <em>IDb CProvable</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.IDbCProvable
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getIDbCProvable()
       * @generated
       */
      EClass IDB_CPROVABLE = eINSTANCE.getIDbCProvable();

      /**
       * The meta object literal for the '<em><b>Proof Obligations</b></em>' reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference IDB_CPROVABLE__PROOF_OBLIGATIONS = eINSTANCE.getIDbCProvable_ProofObligations();

      /**
       * The meta object literal for the '<em><b>All Proofs</b></em>' reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference IDB_CPROVABLE__ALL_PROOFS = eINSTANCE.getIDbCProvable_AllProofs();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable <em>IDb CProof Referencable</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getIDbCProofReferencable()
       * @generated
       */
      EClass IDB_CPROOF_REFERENCABLE = eINSTANCE.getIDbCProofReferencable();

      /**
       * The meta object literal for the '<em><b>All References</b></em>' reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference IDB_CPROOF_REFERENCABLE__ALL_REFERENCES = eINSTANCE.getIDbCProofReferencable_AllReferences();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcProofObligationImpl <em>Dbc Proof Obligation</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcProofObligationImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcProofObligation()
       * @generated
       */
      EClass DBC_PROOF_OBLIGATION = eINSTANCE.getDbcProofObligation();

      /**
       * The meta object literal for the '<em><b>Obligation</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DBC_PROOF_OBLIGATION__OBLIGATION = eINSTANCE.getDbcProofObligation_Obligation();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbcAxiomImpl <em>Dbc Axiom</em>}' class.
       * <!-- begin-user-doc -->
         * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcAxiomImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcAxiom()
       * @generated
       */
        EClass DBC_AXIOM = eINSTANCE.getDbcAxiom();

    /**
       * The meta object literal for the '<em><b>Definition</b></em>' attribute feature.
       * <!-- begin-user-doc -->
         * <!-- end-user-doc -->
       * @generated
       */
        EAttribute DBC_AXIOM__DEFINITION = eINSTANCE.getDbcAxiom_Definition();

    /**
       * The meta object literal for the '<em><b>Axiom Contracts</b></em>' containment reference list feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EReference DBC_AXIOM__AXIOM_CONTRACTS = eINSTANCE.getDbcAxiom_AxiomContracts();

   /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.impl.DbCAxiomContractImpl <em>Db CAxiom Contract</em>}' class.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbCAxiomContractImpl
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbCAxiomContract()
       * @generated
       */
      EClass DB_CAXIOM_CONTRACT = eINSTANCE.getDbCAxiomContract();

   /**
       * The meta object literal for the '<em><b>Pre</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DB_CAXIOM_CONTRACT__PRE = eINSTANCE.getDbCAxiomContract_Pre();

   /**
       * The meta object literal for the '<em><b>Dep</b></em>' attribute feature.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @generated
       */
      EAttribute DB_CAXIOM_CONTRACT__DEP = eINSTANCE.getDbCAxiomContract_Dep();

   /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.DbcVisibility <em>Dbc Visibility</em>}' enum.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.DbcVisibility
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcVisibility()
       * @generated
       */
      EEnum DBC_VISIBILITY = eINSTANCE.getDbcVisibility();

      /**
       * The meta object literal for the '{@link de.hentschel.visualdbc.dbcmodel.DbcProofStatus <em>Dbc Proof Status</em>}' enum.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see de.hentschel.visualdbc.dbcmodel.DbcProofStatus
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getDbcProofStatus()
       * @generated
       */
      EEnum DBC_PROOF_STATUS = eINSTANCE.getDbcProofStatus();

      /**
       * The meta object literal for the '<em>Properties</em>' data type.
       * <!-- begin-user-doc -->
       * <!-- end-user-doc -->
       * @see java.util.Properties
       * @see de.hentschel.visualdbc.dbcmodel.impl.DbcmodelPackageImpl#getProperties()
       * @generated
       */
      EDataType PROPERTIES = eINSTANCE.getProperties();

   }

} //DbcmodelPackage