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

import org.eclipse.emf.ecore.EObject;

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
import de.hentschel.visualdbc.dbcmodel.IDbCProvable;

/**
 * The default {@link IDSFinder} implementation. 
 * @author Martin Hentschel
 */
public class DefaultDSFinder extends AbstractDSFinder {
   /**
    * Constructor.
    * @param connection The {@link IDSConnection} to use.
    */
   public DefaultDSFinder(IDSConnection connection) {
      super(connection);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSClass findClass(DbcClass toSearch) throws DSException {
      IDSClass result = null;
      if (toSearch != null) {
         // Check if it is anonymous
         if (toSearch.isAnonymous()) {
            throw new DSException("Anonymous classes like \"" + toSearch.getName() + "\" are not supported.");
         }
         // Get parent
         EObject parent = toSearch.eContainer();
         if (parent instanceof DbcPackage) {
            IDSPackage dsParent = findPackage((DbcPackage)parent);
            result = dsParent.getClass(toSearch.getName());
         }
         else if (parent instanceof DbcClass) {
            IDSClass dsParent = findClass((DbcClass)parent);
            result = dsParent.getInnerClass(toSearch.getName());
         }
         else if (parent instanceof DbcInterface) {
            IDSInterface dsParent = findInterface((DbcInterface)parent);
            result = dsParent.getInnerClass(toSearch.getName());
         }
         else if (parent instanceof DbcEnum) {
            IDSEnum dsParent = findEnum((DbcEnum)parent);
            result = dsParent.getInnerClass(toSearch.getName());
         }
         else if (parent instanceof DbcModel) {
            result = getConnection().getClass(toSearch.getName());
         }         
         else {
            throw new DSException("Not supported parent: " + parent);
         }
      }
      if (result == null) {
         throw new DSException("Can't find class for: " + toSearch);
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSInterface findInterface(DbcInterface toSearch) throws DSException {
      IDSInterface result = null;
      if (toSearch != null) {
         // Get parent
         EObject parent = toSearch.eContainer();
         if (parent instanceof DbcPackage) {
            IDSPackage dsParent = findPackage((DbcPackage)parent);
            result = dsParent.getInterface(toSearch.getName());
         }
         else if (parent instanceof DbcClass) {
            IDSClass dsParent = findClass((DbcClass)parent);
            result = dsParent.getInnerInterface(toSearch.getName());
         }
         else if (parent instanceof DbcInterface) {
            IDSInterface dsParent = findInterface((DbcInterface)parent);
            result = dsParent.getInnerInterface(toSearch.getName());
         }
         else if (parent instanceof DbcEnum) {
            IDSEnum dsParent = findEnum((DbcEnum)parent);
            result = dsParent.getInnerInterface(toSearch.getName());
         }
         else if (parent instanceof DbcModel) {
            result = getConnection().getInterface(toSearch.getName());
         }         
         else {
            throw new DSException("Not supported parent: " + parent);
         }
      }
      if (result == null) {
         throw new DSException("Can't find interface for: " + toSearch);
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSEnum findEnum(DbcEnum toSearch) throws DSException {
      IDSEnum result = null;
      if (toSearch != null) {
         // Get parent
         EObject parent = toSearch.eContainer();
         if (parent instanceof DbcPackage) {
            IDSPackage dsParent = findPackage((DbcPackage)parent);
            result = dsParent.getEnum(toSearch.getName());
         }
         else if (parent instanceof DbcClass) {
            IDSClass dsParent = findClass((DbcClass)parent);
            result = dsParent.getInnerEnum(toSearch.getName());
         }
         else if (parent instanceof DbcInterface) {
            IDSInterface dsParent = findInterface((DbcInterface)parent);
            result = dsParent.getInnerEnum(toSearch.getName());
         }
         else if (parent instanceof DbcEnum) {
            IDSEnum dsParent = findEnum((DbcEnum)parent);
            result = dsParent.getInnerEnum(toSearch.getName());
         }
         else if (parent instanceof DbcModel) {
            result = getConnection().getEnum(toSearch.getName());
         }         
         else {
            throw new DSException("Not supported parent: " + parent);
         }
      }
      if (result == null) {
         throw new DSException("Can't find enum for: " + toSearch);
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSPackage findPackage(DbcPackage toSearch) throws DSException {
      IDSPackage result = null;
      if (toSearch != null) {
         // Get parent
         EObject parent = toSearch.eContainer();
         if (parent instanceof DbcModel) {
            result = getConnection().getPackage(toSearch.getName());
         }
         else if (parent instanceof DbcPackage) {
            IDSPackage dsParent = findPackage((DbcPackage)parent);
            result = dsParent.getPackage(toSearch.getName());
         }
         else {
            throw new DSException("Not supported parent: " + parent);
         }
      }
      if (result == null) {
         throw new DSException("Can't find package for: " + toSearch);
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSMethod findMethod(DbcMethod toSearch) throws DSException {
      IDSMethod result = null;
      if (toSearch != null) {
         // Get parent
         EObject parent = toSearch.eContainer();
         if (parent instanceof DbcClass) {
            IDSClass dsParent = findClass((DbcClass)parent);
            result = dsParent.getMethod(toSearch.getSignature());
         }
         else if (parent instanceof DbcInterface) {
            IDSInterface dsParent = findInterface((DbcInterface)parent);
            result = dsParent.getMethod(toSearch.getSignature());
         }
         else if (parent instanceof DbcEnum) {
            IDSEnum dsParent = findEnum((DbcEnum)parent);
            result = dsParent.getMethod(toSearch.getSignature());
         }
         else {
            throw new DSException("Not supported parent: " + parent);
         }
      }
      if (result == null) {
         throw new DSException("Can't find method for: " + toSearch);
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSAxiom findAxiom(DbcAxiom toSearch) throws DSException {
      IDSAxiom result = null;
      if (toSearch != null) {
         // Get parent
         EObject parent = toSearch.eContainer();
         if (parent instanceof DbcClass) {
            IDSClass dsParent = findClass((DbcClass)parent);
            result = dsParent.getAxiom(toSearch.getDefinition());
         }
         else if (parent instanceof DbcInterface) {
            IDSInterface dsParent = findInterface((DbcInterface)parent);
            result = dsParent.getAxiom(toSearch.getDefinition());
         }
         else if (parent instanceof DbcEnum) {
            IDSEnum dsParent = findEnum((DbcEnum)parent);
            result = dsParent.getAxiom(toSearch.getDefinition());
         }
         else {
            throw new DSException("Not supported parent: " + parent);
         }
      }
      if (result == null) {
         throw new DSException("Can't find axiom for: " + toSearch);
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSInvariant findInvariant(DbcInvariant toSearch) throws DSException {
      IDSInvariant result = null;
      if (toSearch != null) {
         // Get parent
         EObject parent = toSearch.eContainer();
         if (parent instanceof DbcClass) {
            IDSClass dsParent = findClass((DbcClass)parent);
            result = dsParent.getInvariant(toSearch.getCondition());
         }
         else if (parent instanceof DbcInterface) {
            IDSInterface dsParent = findInterface((DbcInterface)parent);
            result = dsParent.getInvariant(toSearch.getCondition());
         }
         else if (parent instanceof DbcEnum) {
            IDSEnum dsParent = findEnum((DbcEnum)parent);
            result = dsParent.getInvariant(toSearch.getCondition());
         }
         else {
            throw new DSException("Not supported parent: " + parent);
         }
      }
      if (result == null) {
         throw new DSException("Can't find invariant for: " + toSearch);
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSAttribute findAttribute(DbcAttribute toSearch) throws DSException {
      IDSAttribute result = null;
      if (toSearch != null) {
         // Get parent
         EObject parent = toSearch.eContainer();
         if (parent instanceof DbcClass) {
            IDSClass dsParent = findClass((DbcClass)parent);
            result = dsParent.getAttribute(toSearch.getName());
         }
         else if (parent instanceof DbcInterface) {
            IDSInterface dsParent = findInterface((DbcInterface)parent);
            result = dsParent.getAttribute(toSearch.getName());
         }
         else if (parent instanceof DbcEnum) {
            IDSEnum dsParent = findEnum((DbcEnum)parent);
            result = dsParent.getAttribute(toSearch.getName());
         }
         else {
            throw new DSException("Not supported parent: " + parent);
         }
      }
      if (result == null) {
         throw new DSException("Can't find attribute for: " + toSearch);
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSEnumLiteral findEnumLiteral(DbcEnumLiteral toSearch) throws DSException {
      IDSEnumLiteral result = null;
      if (toSearch != null) {
         // Get parent
         EObject parent = toSearch.eContainer();
         if (parent instanceof DbcEnum) {
            IDSEnum dsParent = findEnum((DbcEnum)parent);
            result = dsParent.getLiteral(toSearch.getName());
         }
         else {
            throw new DSException("Not supported parent: " + parent);
         }
      }
      if (result == null) {
         throw new DSException("Can't find enum literal for: " + toSearch);
      }
      return result;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public IDSAxiomContract findAxiomContract(DbCAxiomContract toSearch) throws DSException {
      IDSAxiomContract result = null;
      if (toSearch != null) {
         // Get parent
         EObject parent = toSearch.eContainer();
         if (parent instanceof DbcAxiom) {
            IDSAxiom dsParent = findAxiom((DbcAxiom)parent);
            result = dsParent.getAxiomContract(toSearch.getPre(), toSearch.getDep());
         }
         else {
            throw new DSException("Not supported parent: " + parent);
         }
         if (result == null) {
            throw new DSException("Can't find axiom contract for: " + toSearch);
         }
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSConstructor findConstructor(DbcConstructor toSearch) throws DSException {
      IDSConstructor result = null;
      if (toSearch != null) {
         // Get parent
         EObject parent = toSearch.eContainer();
         if (parent instanceof DbcClass) {
            IDSClass dsParent = findClass((DbcClass)parent);
            result = dsParent.getConstructor(toSearch.getSignature());
         }
         else if (parent instanceof DbcEnum) {
            IDSEnum dsParent = findEnum((DbcEnum)parent);
            result = dsParent.getConstructor(toSearch.getSignature());
         }
         else {
            throw new DSException("Not supported parent: " + parent);
         }
      }
      if (result == null) {
         throw new DSException("Can't find constructor for: " + toSearch);
      }
      return result;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public IDSOperationContract findOperationContract(DbcOperationContract toSearch) throws DSException {
      IDSOperationContract result = null;
      if (toSearch != null) {
         // Get parent
         EObject parent = toSearch.eContainer();
         if (parent instanceof DbcMethod) {
            IDSMethod dsParent = findMethod((DbcMethod)parent);
            result = dsParent.getOperationContract(toSearch.getPre(), toSearch.getPost());
         }
         else if (parent instanceof DbcConstructor) {
            IDSConstructor dsParent = findConstructor((DbcConstructor)parent);
            result = dsParent.getOperationContract(toSearch.getPre(), toSearch.getPost());
         }
         else {
            throw new DSException("Not supported parent: " + parent);
         }
         if (result == null) {
            throw new DSException("Can't find operation contract for: " + toSearch);
         }
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSProvable findProvable(IDbCProvable toSearch) throws DSException {
      IDSProvable result = null;
      if (toSearch != null) {
         // Handle direct model elements
         if (toSearch instanceof DbcClass) {
            result = findClass((DbcClass)toSearch);
         }
         else if (toSearch instanceof DbcEnum) {
            result = findEnum((DbcEnum)toSearch);
         }
         else if (toSearch instanceof DbcInterface) {
            result = findInterface((DbcInterface)toSearch);
         }
         else if (toSearch instanceof DbcMethod) {
            result = findMethod((DbcMethod)toSearch);
         }
         else if (toSearch instanceof DbcConstructor) {
            result = findConstructor((DbcConstructor)toSearch);
         }
         else if (toSearch instanceof DbcOperationContract) {
            result = findOperationContract((DbcOperationContract)toSearch);
         }
         else if (toSearch instanceof DbcAxiom) {
            result = findAxiom((DbcAxiom)toSearch);
         }
         else if (toSearch instanceof DbCAxiomContract) {
            result = findAxiomContract((DbCAxiomContract)toSearch);
         }
         else {
            throw new DSException("Not supported provable: " + toSearch);
         }
      }
      if (result == null) {
         throw new DSException("Can't find provable for: " + toSearch);
      }      
      return result;
   }
}