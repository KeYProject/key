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
import de.hentschel.visualdbc.datasource.model.IDSContainer;
import de.hentschel.visualdbc.datasource.model.IDSEnum;
import de.hentschel.visualdbc.datasource.model.IDSEnumLiteral;
import de.hentschel.visualdbc.datasource.model.IDSInterface;
import de.hentschel.visualdbc.datasource.model.IDSInvariant;
import de.hentschel.visualdbc.datasource.model.IDSMethod;
import de.hentschel.visualdbc.datasource.model.IDSOperation;
import de.hentschel.visualdbc.datasource.model.IDSOperationContract;
import de.hentschel.visualdbc.datasource.model.IDSPackage;
import de.hentschel.visualdbc.datasource.model.IDSProvable;
import de.hentschel.visualdbc.datasource.model.IDSType;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcType;
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
 * The default {@link IDbcFinder} implementation. 
 * @author Martin Hentschel
 */
public class DefaultDbcFinder extends AbstractDbcFinder {
   /**
    * Constructor.
    * @param model The {@link DbcModel} to use.
    */
   public DefaultDbcFinder(DbcModel model) {
      super(model);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public DbcPackage findPackage(IDSPackage toSearch) throws DSException {
      DbcPackage result = null;
      if (toSearch != null) {
         // Get parent
         IDSContainer parent = toSearch.getParent();
         if (parent instanceof IDSConnection) {
            result = getModel().getPackage(toSearch.getName());
         }
         else if (parent instanceof IDSPackage) {
            DbcPackage dbcParent = findPackage((IDSPackage)parent);
            result = dbcParent.getPackage(toSearch.getName());
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
   public DbcClass findClass(IDSClass toSearch) throws DSException {
      // Check if it is anonymous
      if (toSearch != null && toSearch.isAnonymous()) {
         throw new DSException("Anonymous classes like \"" + toSearch.getName() + "\" are not supported.");
      }
      return (DbcClass)findType(toSearch, "Class");
   }

   /**
    * {@inheritDoc}
    */   
   @Override
   public DbcInterface findInterface(IDSInterface toSearch) throws DSException {
      return (DbcInterface)findType(toSearch, "Interface");
   }

   /**
    * {@inheritDoc}
    */   
   @Override
   public DbcEnum findEnum(IDSEnum toSearch) throws DSException {
      return (DbcEnum)findType(toSearch, "Enum");
   }
   
   /**
    * Finds an {@link AbstractDbcType}.
    * @param toSearch The {@link IDSType} to search for.
    * @return The found {@link AbstractDbcType} or a thrown {@link DSException} if no one was found.
    * @throws DSException Occurred Exception.
    */
   protected AbstractDbcType findType(IDSType toSearch, String typeName) throws DSException {
      AbstractDbcType result = null;
      if (toSearch != null) {
         // Get parent package
         IDSContainer parentContainer = toSearch.getParentContainer();
         if (parentContainer != null) {
            if (parentContainer instanceof IDSPackage) {
               DbcPackage dbcParent = findPackage((IDSPackage)parentContainer);
               result = dbcParent.getType(toSearch.getName());
            }
            else if (parentContainer instanceof IDSConnection) {
               result = getModel().getType(toSearch.getName());
            }
            else {
               throw new DSException("Not supported parent: " + parentContainer);
            }
         }
         else {
            // Get inner type parent
            IDSType parentType = toSearch.getParentType();
            if (parentType != null) {
               if (parentType instanceof IDSClass) {
                  DbcClass dbcParent = findClass((IDSClass)parentType);
                  result = dbcParent.getType(toSearch.getName());
               }
               else if (parentType instanceof IDSInterface) {
                  DbcInterface dbcParent = findInterface((IDSInterface)parentType);
                  result = dbcParent.getType(toSearch.getName());
               }
               else if (parentType instanceof IDSEnum) {
                  DbcEnum dbcParent = findEnum((IDSEnum)parentType);
                  result = dbcParent.getType(toSearch.getName());
               }
               else {
                  throw new DSException("Not supported parent: " + parentType);
               }
            }
            else {
               throw new DSException(typeName + " has no parent: " + toSearch);
            }
         }
      }
      if (result == null) {
         throw new DSException("Can't find " + typeName + " for: " + toSearch);
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public DbcMethod findMethod(IDSMethod toSearch) throws DSException {
      DbcMethod result = null;
      if (toSearch != null) {
         // Get parent
         IDSType parent = toSearch.getParent();
         if (parent instanceof IDSClass) {
            DbcClass dbcParent = findClass((IDSClass)parent);
            result = dbcParent.getMethod(toSearch.getSignature());
         }
         else if (parent instanceof IDSInterface) {
            DbcInterface dbcParent = findInterface((IDSInterface)parent);
            result = dbcParent.getMethod(toSearch.getSignature());
         }
         else if (parent instanceof IDSEnum) {
            DbcEnum dbcParent = findEnum((IDSEnum)parent);
            result = dbcParent.getMethod(toSearch.getSignature());
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
   public DbcConstructor findConstructor(IDSConstructor toSearch) throws DSException {
      DbcConstructor result = null;
      if (toSearch != null) {
         // Get parent
         IDSType parent = toSearch.getParent();
         if (parent instanceof IDSClass) {
            DbcClass dbcParent = findClass((IDSClass)parent);
            result = dbcParent.getConstructor(toSearch.getSignature());
         }
         else if (parent instanceof IDSEnum) {
            DbcEnum dbcParent = findEnum((IDSEnum)parent);
            result = dbcParent.getConstructor(toSearch.getSignature());
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
   public DbcOperationContract findOperationContract(IDSOperationContract toSearch) throws DSException {
      DbcOperationContract result = null;
      if (toSearch != null) {
         // Get parent
         IDSOperation parent = toSearch.getParent();
         if (parent instanceof IDSMethod) {
            DbcMethod dbcParent = findMethod((IDSMethod)parent);
            result = dbcParent.getOperationContract(toSearch.getPre(), toSearch.getPost());
         }
         else if (parent instanceof IDSConstructor) {
            DbcConstructor dbcParent = findConstructor((IDSConstructor)parent);
            result = dbcParent.getOperationContract(toSearch.getPre(), toSearch.getPost());
         }
         else {
            throw new DSException("Not supported parent: " + parent);
         }         
      }
      if (result == null) {
         throw new DSException("Can't find operation contract for: " + toSearch);
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public DbcAxiom findAxiom(IDSAxiom toSearch) throws DSException {
      DbcAxiom result = null;
      if (toSearch != null) {
         // Get parent
         IDSType parent = toSearch.getParent();
         if (parent instanceof IDSClass) {
            DbcClass dbcParent = findClass((IDSClass)parent);
            result = dbcParent.getAxiom(toSearch.getDefinition());
         }
         else if (parent instanceof IDSInterface) {
            DbcInterface dbcParent = findInterface((IDSInterface)parent);
            result = dbcParent.getAxiom(toSearch.getDefinition());
         }
         else if (parent instanceof IDSEnum) {
            DbcEnum dbcParent = findEnum((IDSEnum)parent);
            result = dbcParent.getAxiom(toSearch.getDefinition());
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
   public DbcAttribute findAttribute(IDSAttribute toSearch) throws DSException {
      DbcAttribute result = null;
      if (toSearch != null) {
         // Get parent
         IDSType parent = toSearch.getParent();
         if (parent instanceof IDSClass) {
            DbcClass dbcParent = findClass((IDSClass)parent);
            result = dbcParent.getAttribute(toSearch.getName());
         }
         else if (parent instanceof IDSInterface) {
            DbcInterface dbcParent = findInterface((IDSInterface)parent);
            result = dbcParent.getAttribute(toSearch.getName());
         }
         else if (parent instanceof IDSEnum) {
            DbcEnum dbcParent = findEnum((IDSEnum)parent);
            result = dbcParent.getAttribute(toSearch.getName());
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
   public DbcEnumLiteral findEnumLiteral(IDSEnumLiteral toSearch) throws DSException {
      DbcEnumLiteral result = null;
      if (toSearch != null) {
         // Get parent
         IDSEnum parent = toSearch.getParent();
         DbcEnum dbcParent = findEnum((IDSEnum)parent);
         result = dbcParent.getLiteral(toSearch.getName());
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
   public DbCAxiomContract findAxiomContract(IDSAxiomContract toSearch) throws DSException {
      DbCAxiomContract result = null;
      if (toSearch != null) {
         // Get parent
         IDSAxiom parent = toSearch.getParent();
         DbcAxiom dbcParent = findAxiom(parent);
         result = dbcParent.getAxiomContract(toSearch.getPre(), toSearch.getDep());
      }
      if (result == null) {
         throw new DSException("Can't find axiom contract for: " + toSearch);
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public DbcInvariant findInvariant(IDSInvariant toSearch) throws DSException {
      DbcInvariant result = null;
      if (toSearch != null) {
         // Get parent
         IDSType parent = toSearch.getParent();
         if (parent instanceof IDSClass) {
            DbcClass dbcParent = findClass((IDSClass)parent);
            result = dbcParent.getInvariant(toSearch.getCondition());
         }
         else if (parent instanceof IDSInterface) {
            DbcInterface dbcParent = findInterface((IDSInterface)parent);
            result = dbcParent.getInvariant(toSearch.getCondition());
         }
         else if (parent instanceof IDSEnum) {
            DbcEnum dbcParent = findEnum((IDSEnum)parent);
            result = dbcParent.getInvariant(toSearch.getCondition());
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
   public IDbCProvable findProvable(IDSProvable toSearch) throws DSException {
      IDbCProvable result = null;
      if (toSearch != null) {
         // Handle direct model elements
         if (toSearch instanceof IDSClass) {
            result = findClass((IDSClass)toSearch);
         }
         else if (toSearch instanceof IDSEnum) {
            result = findEnum((IDSEnum)toSearch);
         }
         else if (toSearch instanceof IDSInterface) {
            result = findInterface((IDSInterface)toSearch);
         }
         else if (toSearch instanceof IDSMethod) {
            result = findMethod((IDSMethod)toSearch);
         }
         else if (toSearch instanceof IDSConstructor) {
            result = findConstructor((IDSConstructor)toSearch);
         }
         else if (toSearch instanceof IDSOperationContract) {
            result = findOperationContract((IDSOperationContract)toSearch);
         }
         else if (toSearch instanceof IDSAxiomContract) {
            result = findAxiomContract((IDSAxiomContract)toSearch);
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

   /**
    * {@inheritDoc}
    */
   @Override
   public IDbCProofReferencable findProofReferencable(IDSProvable toSearch) throws DSException {
      IDbCProofReferencable result = null;
      if (toSearch != null) {
         if (toSearch instanceof IDSInvariant) {
            result = findInvariant((IDSInvariant)toSearch);
         }
         else if (toSearch instanceof IDSAxiom) {
            result = findAxiom((IDSAxiom)toSearch);
         }
         else if (toSearch instanceof IDSAttribute) {
            result = findAttribute((IDSAttribute)toSearch);
         }
         else if (toSearch instanceof IDSEnumLiteral) {
            result = findEnumLiteral((IDSEnumLiteral)toSearch);
         }
         else {
            result = findProvable(toSearch);
         }
      }
      if (result == null) {
         throw new DSException("Can't find proof referencable for: " + toSearch);
      }      
      return result;
   }
}