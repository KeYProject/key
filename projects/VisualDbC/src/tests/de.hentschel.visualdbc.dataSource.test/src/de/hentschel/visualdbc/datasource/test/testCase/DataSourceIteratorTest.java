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

package de.hentschel.visualdbc.datasource.test.testCase;

import java.util.HashSet;
import java.util.Set;

import junit.framework.TestCase;
import de.hentschel.visualdbc.datasource.model.DSVisibility;
import de.hentschel.visualdbc.datasource.model.IDSAttribute;
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
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.memory.MemoryAttribute;
import de.hentschel.visualdbc.datasource.model.memory.MemoryClass;
import de.hentschel.visualdbc.datasource.model.memory.MemoryConnection;
import de.hentschel.visualdbc.datasource.model.memory.MemoryConstructor;
import de.hentschel.visualdbc.datasource.model.memory.MemoryEnum;
import de.hentschel.visualdbc.datasource.model.memory.MemoryEnumLiteral;
import de.hentschel.visualdbc.datasource.model.memory.MemoryInterface;
import de.hentschel.visualdbc.datasource.model.memory.MemoryInvariant;
import de.hentschel.visualdbc.datasource.model.memory.MemoryMethod;
import de.hentschel.visualdbc.datasource.model.memory.MemoryOperationContract;
import de.hentschel.visualdbc.datasource.model.memory.MemoryPackage;
import de.hentschel.visualdbc.datasource.util.DataSourceIterator;

/**
 * Tests for {@link DataSourceIterator}.
 * @author Martin Hentschel
 */
public class DataSourceIteratorTest extends TestCase {
   /**
    * Tests the iteration over all elements starting with
    * {@link DataSourceIterator#iterateOverConnection(de.hentschel.visualdbc.datasource.model.IDSConnection)}
    */
   public void testIterationOnConnection() {
      try {
         // Create model
         Set<Object> expected = new HashSet<Object>();
         // Fill connection
         MemoryConnection con = new MemoryConnection(null);
         expected.add(con);
         MemoryClass conClass = new MemoryClass("conClass");
         expected.add(conClass);
         con.addClass(conClass);
         MemoryInterface conInterface = new MemoryInterface("conInterface");
         expected.add(conInterface);
         con.addInterface(conInterface);
         MemoryEnum conEnum = new MemoryEnum("conEnum");
         expected.add(conEnum);
         con.addEnum(conEnum);
         MemoryPackage conPackage = new MemoryPackage("conPackage");
         expected.add(conPackage);
         con.addPackage(conPackage);
         // Fill package
         MemoryClass packageClass = new MemoryClass("packageClass");
         expected.add(packageClass);
         conPackage.addClass(packageClass);
         MemoryInterface packageInterface = new MemoryInterface("packageInterface");
         expected.add(packageInterface);
         conPackage.addInterface(packageInterface);
         MemoryEnum packageEnum = new MemoryEnum("packageEnum");
         expected.add(packageEnum);
         conPackage.addEnum(packageEnum);
         MemoryPackage packagePackage = new MemoryPackage("packagePackage");
         expected.add(packagePackage);
         conPackage.addPackage(packagePackage);
         // Fill class
         MemoryClass classClass = new MemoryClass("classClass");
         expected.add(classClass);
         conClass.addInnerClass(classClass);
         MemoryInterface classInterface = new MemoryInterface("classInterface");
         expected.add(classInterface);
         conClass.addInnerInterface(classInterface);
         MemoryEnum classEnum = new MemoryEnum("classEnum");
         expected.add(classEnum);
         conClass.addInnerEnum(classEnum);
         MemoryAttribute conClassAttribute = new MemoryAttribute("conClassAttribute", "", DSVisibility.PRIVATE);
         expected.add(conClassAttribute);
         conClass.getAttributes().add(conClassAttribute);
         MemoryConstructor conClassConsructor = new MemoryConstructor("conClassConsructor", DSVisibility.PUBLIC);
         expected.add(conClassConsructor);
         conClass.addConstructor(conClassConsructor);
         MemoryOperationContract conClassConsructorContract = new MemoryOperationContract("conClassConsructorContract", "", "", "", "");
         expected.add(conClassConsructorContract);
         conClassConsructor.addOperationContract(conClassConsructorContract);
         String conClassConsructorObligation = "conClassConsructorObligation";
         expected.add(conClassConsructorObligation);
         conClassConsructorContract.getObligations().add(conClassConsructorObligation);
         MemoryMethod conClassMethod = new MemoryMethod("conClassConsructor", "", DSVisibility.PUBLIC);
         expected.add(conClassMethod);
         conClass.addMethod(conClassMethod);
         MemoryOperationContract conClassMethodContract = new MemoryOperationContract("conClassMethodContract", "", "", "", "");
         expected.add(conClassMethodContract);
         conClassMethod.addOperationContract(conClassMethodContract);
         String conClassMethodContractObligation = "conClassMethodContractObligation";
         expected.add(conClassMethodContractObligation);
         conClassMethod.getObligations().add(conClassMethodContractObligation);
         MemoryInvariant conClassInvariant = new MemoryInvariant("", "conClassInvariant");
         expected.add(conClassInvariant);
         conClass.getInvariants().add(conClassInvariant);
         String conClassInvariantObligation = "conClassInvariantObligation";
         expected.add(conClassInvariantObligation);
         conClassInvariant.getObligations().add(conClassInvariantObligation);
         String conClassProofObligation = "conClassProofObligation";
         expected.add(conClassProofObligation);
         conClass.getObligations().add(conClassProofObligation);
         // Fill interface
         MemoryClass interfaceClass = new MemoryClass("interfaceClass");
         expected.add(interfaceClass);
         conInterface.addInnerClass(interfaceClass);
         MemoryInterface interfaceInterface = new MemoryInterface("interfaceInterface");
         expected.add(interfaceInterface);
         conInterface.addInnerInterface(interfaceInterface);
         MemoryEnum interfaceEnum = new MemoryEnum("interfaceEnum");
         expected.add(interfaceEnum);
         conInterface.addInnerEnum(interfaceEnum);
         MemoryAttribute conInterfaceAttribute = new MemoryAttribute("conInterfaceAttribute", "", DSVisibility.PRIVATE);
         expected.add(conInterfaceAttribute);
         conInterface.getAttributes().add(conInterfaceAttribute);
         MemoryMethod conInterfaceMethod = new MemoryMethod("conInterfaceConsructor", "", DSVisibility.PUBLIC);
         expected.add(conInterfaceMethod);
         conInterface.addMethod(conInterfaceMethod);
         MemoryOperationContract conInterfaceMethodContract = new MemoryOperationContract("conInterfaceMethodContract", "", "", "", "");
         expected.add(conInterfaceMethodContract);
         conInterfaceMethod.addOperationContract(conInterfaceMethodContract);
         String conInterfaceMethodContractObligation = "conInterfaceMethodContractObligation";
         expected.add(conInterfaceMethodContractObligation);
         conInterfaceMethod.getObligations().add(conInterfaceMethodContractObligation);
         MemoryInvariant conInterfaceInvariant = new MemoryInvariant("", "conInterfaceInvariant");
         expected.add(conInterfaceInvariant);
         conInterface.getInvariants().add(conInterfaceInvariant);
         String conInterfaceInvariantObligation = "conInterfaceInvariantObligation";
         expected.add(conInterfaceInvariantObligation);
         conInterfaceInvariant.getObligations().add(conInterfaceInvariantObligation);
         String conInterfaceProofObligation = "conInterfaceProofObligation";
         expected.add(conInterfaceProofObligation);
         conInterface.getObligations().add(conInterfaceProofObligation);
         // Fill enumeration
         MemoryClass enumClass = new MemoryClass("enumClass");
         expected.add(enumClass);
         conEnum.addInnerClass(enumClass);
         MemoryInterface enumInterface = new MemoryInterface("enumInterface");
         expected.add(enumInterface);
         conEnum.addInnerInterface(enumInterface);
         MemoryEnum enumEnum = new MemoryEnum("enumEnum");
         expected.add(enumEnum);
         conEnum.addInnerEnum(enumEnum);
         MemoryAttribute conEnumAttribute = new MemoryAttribute("conEnumAttribute", "", DSVisibility.PRIVATE);
         expected.add(conEnumAttribute);
         conEnum.getAttributes().add(conEnumAttribute);
         MemoryConstructor conEnumConsructor = new MemoryConstructor("conEnumConsructor", DSVisibility.PUBLIC);
         expected.add(conEnumConsructor);
         conEnum.addConstructor(conEnumConsructor);
         MemoryOperationContract conEnumConsructorContract = new MemoryOperationContract("conEnumConsructorContract", "", "", "", "");
         expected.add(conEnumConsructorContract);
         conEnumConsructor.addOperationContract(conEnumConsructorContract);
         String conEnumConsructorObligation = "conEnumConsructorObligation";
         expected.add(conEnumConsructorObligation);
         conEnumConsructorContract.getObligations().add(conEnumConsructorObligation);
         MemoryMethod conEnumMethod = new MemoryMethod("conEnumConsructor", "", DSVisibility.PUBLIC);
         expected.add(conEnumMethod);
         conEnum.addMethod(conEnumMethod);
         MemoryOperationContract conEnumMethodContract = new MemoryOperationContract("conEnumMethodContract", "", "", "", "");
         expected.add(conEnumMethodContract);
         conEnumMethod.addOperationContract(conEnumMethodContract);
         String conEnumMethodContractObligation = "conEnumMethodContractObligation";
         expected.add(conEnumMethodContractObligation);
         conEnumMethod.getObligations().add(conEnumMethodContractObligation);
         MemoryInvariant conEnumInvariant = new MemoryInvariant("", "conEnumInvariant");
         expected.add(conEnumInvariant);
         conEnum.getInvariants().add(conEnumInvariant);
         String conEnumInvariantObligation = "conEnumInvariantObligation";
         expected.add(conEnumInvariantObligation);
         conEnumInvariant.getObligations().add(conEnumInvariantObligation);
         String conEnumProofObligation = "conEnumProofObligation";
         expected.add(conEnumProofObligation);
         conEnum.getObligations().add(conEnumProofObligation);
         MemoryEnumLiteral conEnumLiteral = new MemoryEnumLiteral();
         expected.add(conEnumLiteral);
         conEnum.getLiterals().add(conEnumLiteral);
         //Iterate over model and log visited objects
         DataSourceIteratorLogger logger = new DataSourceIteratorLogger();
         logger.iterateOverConnection(con);
         // Compare results
         assertEquals(expected.size(), logger.getVisitedObjects().size());
         assertEquals(expected, logger.getVisitedObjects());
      }
      catch (DSException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
   }
   
   /**
    * Implementation of {@link DataSourceIterator} that logs the visited
    * objects and makes sure that every object is only visited once.
    * @author Martin Hentschel
    */
   private static class DataSourceIteratorLogger extends DataSourceIterator {
      /**
       * The visited objects.
       */
      private Set<Object> visitedObjects = new HashSet<Object>();

      /**
       * Returns all visited objects.
       * @return The visited objects.
       */
      public Set<Object> getVisitedObjects() {
         return visitedObjects;
      }

      /**
       * Logs the visit if it is the first visit and fails the test otherwise.
       * @param instance The visited instance.
       */
      protected void logVisit(Object instance) {
         if (visitedObjects.contains(instance)) {
            fail("Object \"" + instance + "\" visited multiple times.");
         }
         visitedObjects.add(instance);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected void workOnConnection(IDSConnection instance) throws DSException {
         logVisit(instance);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected void workOnPackage(IDSPackage instance) throws DSException {
         logVisit(instance);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected void workOnClass(IDSClass instance) throws DSException {
         logVisit(instance);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected void workOnInterface(IDSInterface instance) throws DSException {
         logVisit(instance);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected void workOnEnum(IDSEnum instance) throws DSException {
         logVisit(instance);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected void workOnMethod(IDSMethod instance) throws DSException {
         logVisit(instance);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected void workOnConstructor(IDSConstructor instance)throws DSException {
         logVisit(instance);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected void workOnOperationContract(IDSOperationContract instance) throws DSException {
         logVisit(instance);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected void workOnAttribute(IDSAttribute instance) throws DSException {
         logVisit(instance);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected void workOnInvariant(IDSInvariant instance) throws DSException {
         logVisit(instance);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected void workOnObligation(String instance) throws DSException {
         logVisit(instance);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected void workOnEnumLiteral(IDSEnumLiteral instance) throws DSException {
         logVisit(instance);
      }
   }
}