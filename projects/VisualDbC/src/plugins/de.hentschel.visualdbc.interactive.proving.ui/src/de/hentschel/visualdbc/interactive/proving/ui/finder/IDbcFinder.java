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

package de.hentschel.visualdbc.interactive.proving.ui.finder;

import de.hentschel.visualdbc.datasource.model.IDSAttribute;
import de.hentschel.visualdbc.datasource.model.IDSAxiom;
import de.hentschel.visualdbc.datasource.model.IDSAxiomContract;
import de.hentschel.visualdbc.datasource.model.IDSClass;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSConstructor;
import de.hentschel.visualdbc.datasource.model.IDSEnum;
import de.hentschel.visualdbc.datasource.model.IDSEnumLiteral;
import de.hentschel.visualdbc.datasource.model.IDSInterface;
import de.hentschel.visualdbc.datasource.model.IDSInvariant;
import de.hentschel.visualdbc.datasource.model.IDSMethod;
import de.hentschel.visualdbc.datasource.model.IDSOperationContract;
import de.hentschel.visualdbc.datasource.model.IDSPackage;
import de.hentschel.visualdbc.datasource.model.IDSProvable;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
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
import de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable;
import de.hentschel.visualdbc.dbcmodel.IDbCProvable;

/**
 * <p>
 * Implementation of {@link IDbcFinder} searches the DbC model instance
 * for a given data source instance.
 * </p>
 * <p>
 * They are instantiated via an {@link IDbcFinderFactory}. Implementations should
 * be subclasses of {@link AbstractDbcFinder}. The default {@link IDbcFinder}
 * {@link DefaultDbcFinder} can handle all not {@code null} {@link IDSConnection}s.
 * </p>
 * @author Martin Hentschel
 * @see IDbcFinderFactory
 * @see DefaultDbcFinderFactory
 * @see AbstractDbcFinder
 * @see DefaultDbcFinder
 */
public interface IDbcFinder {
   /**
    * Returns the {@link DbcModel} in that is searched.
    * @return The {@link DbcModel} to search in.
    */
   public DbcModel getModel();

   /**
    * Finds an {@link DbcPackage}.
    * @param toSearch The {@link IDSPackage} to search for.
    * @return The found {@link DbcPackage} or a thrown {@link DSException} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public DbcPackage findPackage(IDSPackage toSearch) throws DSException;
   
   /**
    * Finds an {@link DbcClass}.
    * @param toSearch The {@link IDSClass} to search for.
    * @return The found {@link DbcClass} or a thrown {@link DSException} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public DbcClass findClass(IDSClass toSearch) throws DSException;

   /**
    * Finds an {@link DbcInterface}.
    * @param toSearch The {@link IDSInterface} to search for.
    * @return The found {@link DbcInterface} or a thrown {@link DSException} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public DbcInterface findInterface(IDSInterface toSearch) throws DSException;

   /**
    * Finds an {@link DbcEnum}.
    * @param toSearch The {@link IDSEnum} to search for.
    * @return The found {@link DbcEnum} or a thrown {@link DSException} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public DbcEnum findEnum(IDSEnum toSearch) throws DSException;

   /**
    * Finds an {@link DbcMethod}.
    * @param toSearch The {@link IDSMethod} to search for.
    * @return The found {@link DbcMethod} or a thrown {@link DSException} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public DbcMethod findMethod(IDSMethod toSearch) throws DSException;

   /**
    * Finds an {@link DbcConstructor}.
    * @param toSearch The {@link IDSConstructor} to search for.
    * @return The found {@link DbcConstructor} or a thrown {@link DSException} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public DbcConstructor findConstructor(IDSConstructor toSearch) throws DSException;

   /**
    * Finds an {@link DbcOperationContract}.
    * @param toSearch The {@link IDSOperationContract} to search for.
    * @return The found {@link DbcOperationContract} or a thrown {@link DSException} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public DbcOperationContract findOperationContract(IDSOperationContract toSearch) throws DSException;

   /**
    * Finds an {@link DbcInvariant}.
    * @param toSearch The {@link IDSInvariant} to search for.
    * @return The found {@link DbcInvariant} or a thrown {@link DSException} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public DbcInvariant findInvariant(IDSInvariant toSearch) throws DSException;

   /**
    * Finds an {@link DbcAxiom}.
    * @param toSearch The {@link IDSAxiom} to search for.
    * @return The found {@link DbcAxiom} or a thrown {@link DSException} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public DbcAxiom findAxiom(IDSAxiom toSearch) throws DSException;

   /**
    * Finds an {@link DbCAxiomContract}.
    * @param toSearch The {@link IDSAxiomContract} to search for.
    * @return The found {@link DbCAxiomContract} or a thrown {@link DSException} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public DbCAxiomContract findAxiomContract(IDSAxiomContract toSearch) throws DSException;
   
   /**
    * Finds an {@link IDbCProvable}.
    * @param toSearch The {@link IDSProvable} to search for.
    * @return The found {@link IDbCProvable} or a thrown {@link DSException} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public IDbCProvable findProvable(IDSProvable toSearch) throws DSException;
   
   /**
    * Finds an {@link IDbCProofReferencable}.
    * @param toSearch The {@link IDSProvable} to search for.
    * @return The found {@link IDbCProofReferencable} or a thrown {@link DSException} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public IDbCProofReferencable findProofReferencable(IDSProvable toSearch) throws DSException;

   /**
    * Finds an {@link DbcAttribute}.
    * @param toSearch The {@link IDSAttribute} to search for.
    * @return The found {@link DbcAttribute} or a thrown {@link DSException} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public DbcAttribute findAttribute(IDSAttribute toSearch) throws DSException;

   /**
    * Finds an {@link DbcEnumLiteral}.
    * @param toSearch The {@link IDSEnumLiteral} to search for.
    * @return The found {@link DbcEnumLiteral} or a thrown {@link DSException} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public DbcEnumLiteral findEnumLiteral(IDSEnumLiteral toSearch) throws DSException;
}