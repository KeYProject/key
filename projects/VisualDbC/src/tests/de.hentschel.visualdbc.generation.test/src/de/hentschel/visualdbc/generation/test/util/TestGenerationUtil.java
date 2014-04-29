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

package de.hentschel.visualdbc.generation.test.util;

import static org.junit.Assert.fail;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.jface.viewers.ISelection;
import org.key_project.util.java.CollectionUtil;

import de.hentschel.visualdbc.datasource.model.DSVisibility;
import de.hentschel.visualdbc.datasource.model.IDSAttribute;
import de.hentschel.visualdbc.datasource.model.IDSAxiom;
import de.hentschel.visualdbc.datasource.model.IDSAxiomContract;
import de.hentschel.visualdbc.datasource.model.IDSClass;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSConnectionSetting;
import de.hentschel.visualdbc.datasource.model.IDSConstructor;
import de.hentschel.visualdbc.datasource.model.IDSDriver;
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
import de.hentschel.visualdbc.datasource.test.util.TestDataSourceUtil;
import de.hentschel.visualdbc.datasource.util.DataSourceIterator;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation;
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
import de.hentschel.visualdbc.dbcmodel.DbcProofObligation;
import de.hentschel.visualdbc.dbcmodel.DbcVisibility;
import de.hentschel.visualdbc.dbcmodel.IDbCProvable;

/**
 * Provides static methods that make testing easier.
 * @author Martin Hentschel
 */
public final class TestGenerationUtil {
   /**
    * Forbid instances.
    */
   private TestGenerationUtil() {
   }

   
   /**
    * Returns an opened data source connection to the dummy model.
    * @return The opened {@link IDSConnection}.
    */
   public static IDSConnection createDummyConnection() {
      try {
         // Get driver
         IDSDriver driver = TestDataSourceUtil.getDummyDriver();
         TestCase.assertNotNull(driver);
         // Create connection
         IDSConnection connection = driver.createConnection();
         TestCase.assertNotNull(connection);
         connection.connect(Collections.<String, Object>emptyMap(), false, new NullProgressMonitor());
         TestCase.assertTrue(connection.isConnected());
         TestCase.assertFalse(connection.isInteractive());
         return connection;
      }
      catch (DSException e) {
         e.printStackTrace();
         TestCase.fail(e.getMessage());
         return null;
      }
   }
   
   /**
    * Closes the given {@link IDSConnection}.
    * @param connection The {@link IDSConnection} to close.
    */
   public static void closeConnection(IDSConnection connection) {
      try {
         if (connection != null) {
            connection.disconnect();
            TestCase.assertFalse(connection.isConnected());
         }
      }
      catch (DSException e) {
         e.printStackTrace();
         TestCase.fail(e.getMessage());
      }
   }

   /**
    * Opens an existing dbc model file.
    * @param modelFile The model file to open.
    * @return The {@link DbcModel} of the opened model file.
    */
   public static DbcModel openDbcModel(IFile modelFile) {
      TestCase.assertNotNull(modelFile);
      TestCase.assertTrue(modelFile.exists());
      ResourceSet rst = new ResourceSetImpl();
      Resource resource = rst.getResource(URI.createPlatformResourceURI(modelFile.getFullPath().toString(), true), true);
      TestCase.assertTrue(resource.getContents().size() == 1);
      EObject firstObject = resource.getContents().get(0); 
      TestCase.assertTrue(firstObject instanceof DbcModel);
      return (DbcModel)firstObject;
   }
   
   /**
    * Compares the data source connection with the model.
    * @param dsConnection The expected data connection.
    * @param dbcModel The current model.
    * @throws DSException Occurred Exception
    */   
   public static void compareModel(IDSConnection dsConnection, DbcModel dbcModel) throws DSException {
      // Compare connection settings
      IDSDriver driver = dsConnection.getDriver(); 
      if (driver != null) {
         TestCase.assertEquals(driver.getId(), dbcModel.getDriverId());
         TestCase.assertNotNull(dsConnection.getConnectionSettings());
         if (dsConnection.getConnectionSettings() != null) {
            Map<String, Object> reloadedSettings = driver.fromPersistentProperties(dbcModel.toConnectionProperties());
            Set<Entry<String, Object>> expectedEntries = dsConnection.getConnectionSettings().entrySet();
            TestCase.assertEquals(expectedEntries.size(), reloadedSettings.size());
            for (Entry<String, Object> expectedEntry : expectedEntries) {
               TestCase.assertTrue(reloadedSettings.containsKey(expectedEntry.getKey()));
               TestCase.assertEquals(expectedEntry.getKey(), expectedEntry.getValue(), reloadedSettings.get(expectedEntry.getKey()));
            }
         }
         else {
            TestCase.assertEquals(0, dbcModel.getConnectionSettings().size());
         }
      }
      // Compare packages
      TestCase.assertEquals(dsConnection.getPackages().size(), dbcModel.getPackages().size());
      Iterator<IDSPackage> dsPackages = dsConnection.getPackages().iterator();
      Iterator<DbcPackage> dbcPackages = dbcModel.getPackages().iterator();
      while (dsPackages.hasNext() && dbcPackages.hasNext()) {
         comparePackage(dsPackages.next(), dbcPackages.next(), true);
      }
      // Compare types
      compareTypes(dsConnection.getClasses(), dsConnection.getEnums(), dsConnection.getInterfaces(), dbcModel.getTypes());
      // Compare proof obligations
      compareProofObligations(dsConnection, dbcModel);
   }

   /**
    * Compares the proof obligations of the given instances.
    * @param dsConnection The data source instance.
    * @param dbcModel The model instance.
    * @throws DSException Occurred Exception.
    */
   public static void compareProofObligations(IDSConnection dsConnection, DbcModel dbcModel) throws DSException {
      TestCase.assertNotNull(dsConnection);
      TestCase.assertNotNull(dbcModel);
      // Collect all available proof obligations in the data source
      final Set<String> ALL_DS_OBLIGATIONS = new HashSet<String>();
      DataSourceIterator iterator = new DataSourceIterator() {
         @Override
         protected void workOnClass(IDSClass instance) throws DSException {
            ALL_DS_OBLIGATIONS.addAll(instance.getObligations());
         }

         @Override
         protected void workOnInterface(IDSInterface instance) throws DSException {
            ALL_DS_OBLIGATIONS.addAll(instance.getObligations());
         }

         @Override
         protected void workOnEnum(IDSEnum instance) throws DSException {
            ALL_DS_OBLIGATIONS.addAll(instance.getObligations());
         }

         @Override
         protected void workOnMethod(IDSMethod instance) throws DSException {
            ALL_DS_OBLIGATIONS.addAll(instance.getObligations());
         }

         @Override
         protected void workOnConstructor(IDSConstructor instance) throws DSException {
            ALL_DS_OBLIGATIONS.addAll(instance.getObligations());
         }

         @Override
         protected void workOnInvariant(IDSInvariant instance) throws DSException {
            ALL_DS_OBLIGATIONS.addAll(instance.getObligations());
         }

         @Override
         protected void workOnOperationContract(IDSOperationContract instance) throws DSException {
            ALL_DS_OBLIGATIONS.addAll(instance.getObligations());
         }

         @Override
         protected void workOnAxiomContract(IDSAxiomContract instance) throws DSException {
            ALL_DS_OBLIGATIONS.addAll(instance.getObligations());
         }
      };
      iterator.iterateOverConnection(dsConnection);
      // Compare obligations
      TestCase.assertEquals(ALL_DS_OBLIGATIONS.size(), dbcModel.getProofObligations().size());
      for (String dsObligation : ALL_DS_OBLIGATIONS) {
         DbcProofObligation dbcObligation = dbcModel.getProofObligation(dsObligation);
         TestCase.assertNotNull(dbcObligation);
         TestCase.assertEquals(dsObligation, dbcObligation.getObligation());
      }
   }


   /**
    * Compares the data source constructor with the model constructor.
    * @param dsConstructor The expected data source constructor.
    * @param dbcConstructor The current model constructor.
    * @param compareReferences Compare references?
    * @throws DSException Occurred Exception
    */   
   public static void compareConstructor(IDSConstructor dsConstructor, DbcConstructor dbcConstructor, boolean compareReferences) throws DSException {
      TestCase.assertNotNull(dsConstructor);
      TestCase.assertNotNull(dbcConstructor);
      compareProvable(dsConstructor, dbcConstructor);
      TestCase.assertEquals(dsConstructor.isStatic(), dbcConstructor.isStatic());
      TestCase.assertEquals(dsConstructor.getSignature(), dbcConstructor.getSignature());
      compareVisibility(dsConstructor.getVisibility(), dbcConstructor.getVisibility());
      // Compare contained operation contracts
      if (compareReferences) {
         TestCase.assertEquals(dsConstructor.getOperationContracts().size(), dbcConstructor.getOperationContracts().size());
         Iterator<IDSOperationContract> dsOperationContracts = dsConstructor.getOperationContracts().iterator();
         Iterator<DbcOperationContract> dbcOperationContracts = dbcConstructor.getOperationContracts().iterator();
         while (dsOperationContracts.hasNext() && dbcOperationContracts.hasNext()) {
            compareOperationContract(dsOperationContracts.next(), dbcOperationContracts.next());
         }
      }
      compareOperationParent(dsConstructor, dbcConstructor);
   }

   /**
    * Compares the data source method with the model method.
    * @param dsMethod The expected data source method.
    * @param dbcMethod The current model method.
    * @param compareReferences Compare references?
    * @throws DSException Occurred Exception
    */   
   public static void compareMethod(IDSMethod dsMethod, DbcMethod dbcMethod, boolean compareReferences) throws DSException {
      TestCase.assertNotNull(dsMethod);
      TestCase.assertNotNull(dbcMethod);
      compareProvable(dsMethod, dbcMethod);
      TestCase.assertEquals(dsMethod.isFinal(), dbcMethod.isFinal());
      TestCase.assertEquals(dsMethod.isStatic(), dbcMethod.isStatic());
      TestCase.assertEquals(dsMethod.isAbstract(), dbcMethod.isAbstract());
      TestCase.assertEquals(dsMethod.getSignature(), dbcMethod.getSignature());
      TestCase.assertEquals(dsMethod.getReturnType(), dbcMethod.getReturnType());
      compareVisibility(dsMethod.getVisibility(), dbcMethod.getVisibility());
      // Compare contained operation contracts
      if (compareReferences) {
         TestCase.assertEquals(dsMethod.getOperationContracts().size(), dbcMethod.getOperationContracts().size());
         Iterator<IDSOperationContract> dsOperationContracts = dsMethod.getOperationContracts().iterator();
         Iterator<DbcOperationContract> dbcOperationContracts = dbcMethod.getOperationContracts().iterator();
         while (dsOperationContracts.hasNext() && dbcOperationContracts.hasNext()) {
            compareOperationContract(dsOperationContracts.next(), dbcOperationContracts.next());
         }
      }
      compareOperationParent(dsMethod, dbcMethod);
   }

   /**
    * Compares the data source enumeration literal with the model enumeration literal.
    * @param dsEnumLiteral The expected data source enumeration literal.
    * @param dbcEnumLiteral The current model enumeration literal.
    * @param compareReferences Compare references?
    * @throws DSException Occurred Exception
    */   
   public static void compareEnumLiteral(IDSEnumLiteral dsEnumLiteral, DbcEnumLiteral dbcEnumLiteral, boolean compareReferences) throws DSException {
      TestCase.assertNotNull(dsEnumLiteral);
      TestCase.assertNotNull(dbcEnumLiteral);
      TestCase.assertEquals(dsEnumLiteral.getName(), dbcEnumLiteral.getName());
      // Compare parent
      if (compareReferences) {
         if (dsEnumLiteral.getParent() instanceof IDSClass) {
            TestCase.assertTrue(dbcEnumLiteral.eContainer() instanceof DbcClass);
            compareClass((IDSClass)dsEnumLiteral.getParent(), (DbcClass)dbcEnumLiteral.eContainer(), false);
         }
         else if (dsEnumLiteral.getParent() instanceof IDSInterface) {
            TestCase.assertTrue(dbcEnumLiteral.eContainer() instanceof DbcInterface);
            compareInterface((IDSInterface)dsEnumLiteral.getParent(), (DbcInterface)dbcEnumLiteral.eContainer(), false);
         }
         else if (dsEnumLiteral.getParent() instanceof IDSEnum) {
            TestCase.assertTrue(dbcEnumLiteral.eContainer() instanceof DbcEnum);
            compareEnum((IDSEnum)dsEnumLiteral.getParent(), (DbcEnum)dbcEnumLiteral.eContainer(), false);
         }
         else {
            fail("Data source type \"" + dsEnumLiteral + "\" has no parent.");
         }
      }
   }
   
   /**
    * Compares the data source attribute with the model attribute.
    * @param dsAttribute The expected data source attribute.
    * @param dbcAttribute The current model attribute.
    * @param compareReferences Compare references?
    * @throws DSException Occurred Exception
    */   
   public static void compareAttribute(IDSAttribute dsAttribute, DbcAttribute dbcAttribute, boolean compareReferences) throws DSException {
      TestCase.assertNotNull(dsAttribute);
      TestCase.assertNotNull(dbcAttribute);
      TestCase.assertEquals(dsAttribute.isFinal(), dbcAttribute.isFinal());
      TestCase.assertEquals(dsAttribute.isStatic(), dbcAttribute.isStatic());
      TestCase.assertEquals(dsAttribute.getName(), dbcAttribute.getName());
      TestCase.assertEquals(dsAttribute.getType(), dbcAttribute.getType());
      compareVisibility(dsAttribute.getVisibility(), dbcAttribute.getVisibility());
      // Compare parent
      if (compareReferences) {
         if (dsAttribute.getParent() instanceof IDSClass) {
            TestCase.assertTrue(dbcAttribute.eContainer() instanceof DbcClass);
            compareClass((IDSClass)dsAttribute.getParent(), (DbcClass)dbcAttribute.eContainer(), false);
         }
         else if (dsAttribute.getParent() instanceof IDSInterface) {
            TestCase.assertTrue(dbcAttribute.eContainer() instanceof DbcInterface);
            compareInterface((IDSInterface)dsAttribute.getParent(), (DbcInterface)dbcAttribute.eContainer(), false);
         }
         else if (dsAttribute.getParent() instanceof IDSEnum) {
            TestCase.assertTrue(dbcAttribute.eContainer() instanceof DbcEnum);
            compareEnum((IDSEnum)dsAttribute.getParent(), (DbcEnum)dbcAttribute.eContainer(), false);
         }
         else {
            fail("Data source type \"" + dsAttribute + "\" has no parent.");
         }
      }
   }

   /**
    * Compares the data source type invariant with the model specification.
    * @param dsTypeInvariant The expected data source type invariant.
    * @param dbcInvariant The current model specification.
    * @throws DSException Occurred Exception
    */
   public static void compareInvariant(IDSInvariant dsTypeInvariant, DbcInvariant dbcInvariant) throws DSException {
      TestCase.assertNotNull(dsTypeInvariant);
      TestCase.assertNotNull(dbcInvariant);
      TestCase.assertEquals(dsTypeInvariant.getName(), dbcInvariant.getName());
      TestCase.assertEquals(dsTypeInvariant.getCondition(), dbcInvariant.getCondition());
      // Compare parent
      if (dsTypeInvariant.getParent() instanceof IDSClass) {
         TestCase.assertTrue(dbcInvariant.eContainer() instanceof DbcClass);
         compareClass((IDSClass)dsTypeInvariant.getParent(), (DbcClass)dbcInvariant.eContainer(), false);
      }
      else if (dsTypeInvariant.getParent() instanceof IDSInterface) {
         TestCase.assertTrue(dbcInvariant.eContainer() instanceof DbcInterface);
         compareInterface((IDSInterface)dsTypeInvariant.getParent(), (DbcInterface)dbcInvariant.eContainer(), false);
      }
      else if (dsTypeInvariant.getParent() instanceof IDSEnum) {
         TestCase.assertTrue(dbcInvariant.eContainer() instanceof DbcEnum);
         compareEnum((IDSEnum)dsTypeInvariant.getParent(), (DbcEnum)dbcInvariant.eContainer(), false);
      }
      else {
         fail("Data source type \"" + dsTypeInvariant + "\" has no parent.");
      }
   }

   /**
    * Compares the given constructor {@link List}s.
    * @param expected The expected values.
    * @param current The current values.
    * @param compareReferences Compare references?
    * @throws DSException Occurred Exception
    */      
   public static void compareAxioms(List<IDSAxiom> expected, List<DbcAxiom> current, boolean compareReferences) throws DSException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.size(), current.size());
      Iterator<IDSAxiom> exClassIter = expected.iterator();
      Iterator<DbcAxiom> curClassIter = current.iterator();
      while (exClassIter.hasNext() && curClassIter.hasNext()) {
         compareAxiom(exClassIter.next(), curClassIter.next(), compareReferences);
      }
      TestCase.assertFalse(exClassIter.hasNext());
      TestCase.assertFalse(curClassIter.hasNext());
   }
   
   /**
    * Compares the given invariants {@link List}s.
    * @param expected The expected values.
    * @param current The current values.
    * @throws DSException Occurred Exception
    */ 
   public static void compareAxioms(List<IDSAxiom> expected, List<IDSAxiom> current) throws DSException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.size(), current.size());
      Iterator<IDSAxiom> exClassIter = expected.iterator();
      Iterator<IDSAxiom> curClassIter = current.iterator();
      while (exClassIter.hasNext() && curClassIter.hasNext()) {
         compareAxiom(true, exClassIter.next(), curClassIter.next());
      }
      TestCase.assertFalse(exClassIter.hasNext());
      TestCase.assertFalse(curClassIter.hasNext());
   }

   /**
    * Compares the data source type invariant with the model specification.
    * @param dsTypeAxiom The expected data source type invariant.
    * @param dbcAxiom The current model specification.
    * @param compareReferences compare also references?
    * @throws DSException Occurred Exception
    */
   public static void compareAxiom(IDSAxiom dsTypeAxiom, DbcAxiom dbcAxiom, boolean compareReferences) throws DSException {
      TestCase.assertNotNull(dsTypeAxiom);
      TestCase.assertNotNull(dbcAxiom);
      TestCase.assertEquals(dsTypeAxiom.getName(), dbcAxiom.getName());
      TestCase.assertEquals(dsTypeAxiom.getDefinition(), dbcAxiom.getDefinition());
      if (compareReferences) {
         // Compare parent
         if (dsTypeAxiom.getParent() instanceof IDSClass) {
            TestCase.assertTrue(dbcAxiom.eContainer() instanceof DbcClass);
            compareClass((IDSClass)dsTypeAxiom.getParent(), (DbcClass)dbcAxiom.eContainer(), false);
         }
         else if (dsTypeAxiom.getParent() instanceof IDSInterface) {
            TestCase.assertTrue(dbcAxiom.eContainer() instanceof DbcInterface);
            compareInterface((IDSInterface)dsTypeAxiom.getParent(), (DbcInterface)dbcAxiom.eContainer(), false);
         }
         else if (dsTypeAxiom.getParent() instanceof IDSEnum) {
            TestCase.assertTrue(dbcAxiom.eContainer() instanceof DbcEnum);
            compareEnum((IDSEnum)dsTypeAxiom.getParent(), (DbcEnum)dbcAxiom.eContainer(), false);
         }
         else {
            fail("Data source type \"" + dsTypeAxiom + "\" has no parent.");
         }
         // Compare contained axiom contracts
         TestCase.assertEquals(dsTypeAxiom.getAxiomContracts().size(), dbcAxiom.getAxiomContracts().size());
         Iterator<IDSAxiomContract> dsOperationContracts = dsTypeAxiom.getAxiomContracts().iterator();
         Iterator<DbCAxiomContract> dbcOperationContracts = dbcAxiom.getAxiomContracts().iterator();
         while (dsOperationContracts.hasNext() && dbcOperationContracts.hasNext()) {
            compareAxiomContract(dsOperationContracts.next(), dbcOperationContracts.next());
         }
      }
   }

   /**
    * Compares the given {@link IDSInvariant}s.
    * @param expected The expected values.
    * @param current The current values.
    * @throws DSException Occurred Exception
    */   
   public static void compareAxiom(boolean compareReferences, IDSAxiom expected, IDSAxiom current) throws DSException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.getName(), current.getName());
      TestCase.assertEquals(expected.getDefinition(), current.getDefinition());
      compareProofObligations(expected.getName(), expected.getObligations(), current.getObligations());
      // Compare parent
      if (expected.getParent() instanceof IDSClass) {
         TestCase.assertTrue(current.getParent() instanceof IDSClass);
         compareClass((IDSClass)expected.getParent(), (IDSClass)current.getParent(), false);
      }
      else if (expected.getParent() instanceof IDSInterface) {
         TestCase.assertTrue(current.getParent() instanceof IDSInterface);
         compareInterface((IDSInterface)expected.getParent(), (IDSInterface)current.getParent(), false);
      }
      else if (expected.getParent() instanceof IDSEnum) {
         TestCase.assertTrue(current.getParent() instanceof IDSEnum);
         compareEnum((IDSEnum)expected.getParent(), (IDSEnum)current.getParent(), false);
      }
      else {
         TestCase.fail("Unsupported parent \"" + expected.getParent() + "\".");
      }
      // Compare axiom contracts
      if (compareReferences) {
         TestCase.assertNotNull(expected);
         TestCase.assertNotNull(current);
         TestCase.assertEquals(expected.getAxiomContracts().size(), current.getAxiomContracts().size());
         Iterator<IDSAxiomContract> exClassIter = expected.getAxiomContracts().iterator();
         Iterator<IDSAxiomContract> curClassIter = current.getAxiomContracts().iterator();
         while (exClassIter.hasNext() && curClassIter.hasNext()) {
            compareAxiomContract(exClassIter.next(), curClassIter.next());
         }
         TestCase.assertFalse(exClassIter.hasNext());
         TestCase.assertFalse(curClassIter.hasNext());
      }
   }
   
   /**
    * Compares the data source operation contract with the model specification.
    * @param dsAxiomContract The expected data source operation contract.
    * @param dbcAxiomContract The current model operation contract.
    * @throws DSException Occurred Exception
    */
   public static void compareAxiomContract(IDSAxiomContract dsAxiomContract, IDSAxiomContract dbcAxiomContract) throws DSException {
      TestCase.assertNotNull(dsAxiomContract);
      TestCase.assertNotNull(dbcAxiomContract);
      compareProofObligations(dsAxiomContract.getName(), dsAxiomContract.getObligations(), dbcAxiomContract.getObligations());
      TestCase.assertEquals(dsAxiomContract.getName(), dbcAxiomContract.getName());
      TestCase.assertEquals(dsAxiomContract.getDep(), dbcAxiomContract.getDep());
      TestCase.assertEquals(dsAxiomContract.getPre(), dbcAxiomContract.getPre());
      // Compare parent
      TestCase.assertNotNull(dbcAxiomContract.getParent());
      compareAxiom(false, dsAxiomContract.getParent(), dbcAxiomContract.getParent());
   }
   
   /**
    * Compares the data source operation contract with the model specification.
    * @param dsAxiomContract The expected data source operation contract.
    * @param dbcAxiomContract The current model operation contract.
    * @throws DSException Occurred Exception
    */
   public static void compareAxiomContract(IDSAxiomContract dsAxiomContract, DbCAxiomContract dbcAxiomContract) throws DSException {
      TestCase.assertNotNull(dsAxiomContract);
      TestCase.assertNotNull(dbcAxiomContract);
      compareProvable(dsAxiomContract, dbcAxiomContract);
      TestCase.assertEquals(dsAxiomContract.getName(), dbcAxiomContract.getName());
      TestCase.assertEquals(dsAxiomContract.getDep(), dbcAxiomContract.getDep());
      TestCase.assertEquals(dsAxiomContract.getPre(), dbcAxiomContract.getPre());
      // Compare parent
      TestCase.assertTrue(dbcAxiomContract.eContainer() instanceof DbcAxiom);
      compareAxiom(dsAxiomContract.getParent(), (DbcAxiom)dbcAxiomContract.eContainer(), false);
   }
   
   /**
    * Compares the data source operation contract with the model specification.
    * @param dsOperationContract The expected data source operation contract.
    * @param dbcOperationContract The current model operation contract.
    * @throws DSException Occurred Exception
    */
   public static void compareOperationContract(IDSOperationContract dsOperationContract, DbcOperationContract dbcOperationContract) throws DSException {
      TestCase.assertNotNull(dsOperationContract);
      TestCase.assertNotNull(dbcOperationContract);
      TestCase.assertEquals(dsOperationContract.getModifies(), dbcOperationContract.getModifies());
      compareProvable(dsOperationContract, dbcOperationContract);
      TestCase.assertEquals(dsOperationContract.getName(), dbcOperationContract.getName());
      TestCase.assertEquals(dsOperationContract.getPost(), dbcOperationContract.getPost());
      TestCase.assertEquals(dsOperationContract.getPre(), dbcOperationContract.getPre());
      TestCase.assertEquals(dsOperationContract.getTermination(), dbcOperationContract.getTermination());
      // Compare parent
      if (dsOperationContract.getParent() instanceof IDSMethod) {
         TestCase.assertTrue(dbcOperationContract.eContainer() instanceof DbcMethod);
         compareMethod((IDSMethod)dsOperationContract.getParent(), (DbcMethod)dbcOperationContract.eContainer(), false);
      }
      else if (dsOperationContract.getParent() instanceof IDSConstructor) {
         TestCase.assertTrue(dbcOperationContract.eContainer() instanceof DbcConstructor);
         compareConstructor((IDSConstructor)dsOperationContract.getParent(), (DbcConstructor)dbcOperationContract.eContainer(), false);
      }
      else {
         fail("Data source type \"" + dsOperationContract + "\" has no parent.");
      }      
   }
   
   /**
    * Compares the type lists with each other.
    * @param dsClasses The expected classes.
    * @param dsEnums The expected enumerations.
    * @param dsInterfaces The expected interfaces.
    * @param dbcTypes The current types.
    * @throws DSException Occurred Exception
    */
   public static void compareTypes(List<IDSClass> dsClasses, 
                                   List<IDSEnum> dsEnums, 
                                   List<IDSInterface> dsInterfaces, 
                                   List<AbstractDbcType> dbcTypes) throws DSException {
      TestCase.assertEquals(dsClasses.size() + dsEnums.size() + dsInterfaces.size(), dbcTypes.size());
      Iterator<IDSClass> dsClassesIter = dsClasses.iterator();
      Iterator<IDSEnum> dsEnumsIter = dsEnums.iterator();
      Iterator<IDSInterface> dsInterfacesIter = dsInterfaces.iterator();
      Iterator<AbstractDbcType> dbcTypesIter = dbcTypes.iterator();
      while (dbcTypesIter.hasNext()) {
         AbstractDbcType dbcType = dbcTypesIter.next();
         if (dbcType instanceof DbcClass) {
            TestCase.assertTrue(dsClassesIter.hasNext());
            compareClass(dsClassesIter.next(), (DbcClass)dbcType, true);
         }
         else if (dbcType instanceof DbcInterface) {
            TestCase.assertTrue(dsInterfacesIter.hasNext());
            compareInterface(dsInterfacesIter.next(), (DbcInterface)dbcType, true);
         }
         else if (dbcType instanceof DbcEnum) {
            TestCase.assertTrue(dsEnumsIter.hasNext());
            compareEnum(dsEnumsIter.next(), (DbcEnum)dbcType, true);
         }
         else {
            TestCase.fail("Unsupported type \"" + dbcType + "\".");
         }
      }
   }

   /**
    * Compares the data source enumeration with the model enumeration.
    * @param dsEnum The expected data source enumeration.
    * @param dbcEnum The current model enumeration.
    * @throws DSException Occurred Exception
    */   
   public static void compareEnum(IDSEnum dsEnum, DbcEnum dbcEnum, boolean compareReferences) throws DSException {
      TestCase.assertNotNull(dsEnum);
      TestCase.assertNotNull(dbcEnum);
      TestCase.assertEquals(dsEnum.isStatic(), dbcEnum.isStatic());
      TestCase.assertEquals(dsEnum.getName(), dbcEnum.getName());
      compareProvable(dsEnum, dbcEnum);
      compareVisibility(dsEnum.getVisibility(), dbcEnum.getVisibility());
      // Compare axioms
      compareAxioms(dsEnum.getAxioms(), dbcEnum.getAxioms(), compareReferences);
      // Compare inner types
      if (compareReferences) {
         compareTypes(dsEnum.getInnerClasses(), dsEnum.getInnerEnums(), dsEnum.getInnerInterfaces(), dbcEnum.getTypes());
      }
      // Compare contained attributes
      TestCase.assertEquals(dsEnum.getAttributes().size(), dbcEnum.getAttributes().size());
      Iterator<IDSAttribute> dsAttributes = dsEnum.getAttributes().iterator();
      Iterator<DbcAttribute> dbcAttributes = dbcEnum.getAttributes().iterator();
      while (dsAttributes.hasNext() && dbcAttributes.hasNext()) {
         compareAttribute(dsAttributes.next(), dbcAttributes.next(), compareReferences);
      }
      if (compareReferences) {
         // Compare contained methods
         TestCase.assertEquals(dsEnum.getMethods().size(), dbcEnum.getMethods().size());
         Iterator<IDSMethod> dsMethods = dsEnum.getMethods().iterator();
         Iterator<DbcMethod> dbcMethods = dbcEnum.getMethods().iterator();
         while (dsMethods.hasNext() && dbcMethods.hasNext()) {
            compareMethod(dsMethods.next(), dbcMethods.next(), true);
         }
         // Compare contained constructors
         TestCase.assertEquals(dsEnum.getConstructors().size(), dbcEnum.getConstructors().size());
         Iterator<IDSConstructor> dsConstructors = dsEnum.getConstructors().iterator();
         Iterator<DbcConstructor> dbcConstructors = dbcEnum.getConstructors().iterator();
         while (dsConstructors.hasNext() && dbcConstructors.hasNext()) {
            compareConstructor(dsConstructors.next(), dbcConstructors.next(), true);
         }
      }
      // Compare contained literals
      TestCase.assertEquals(dsEnum.getLiterals().size(), dbcEnum.getLiterals().size());
      Iterator<IDSEnumLiteral> dsEnumLiterals = dsEnum.getLiterals().iterator();
      Iterator<DbcEnumLiteral> dbcEnumLiterals = dbcEnum.getLiterals().iterator();
      while (dsEnumLiterals.hasNext() && dbcEnumLiterals.hasNext()) {
         compareEnumLiteral(dsEnumLiterals.next(), dbcEnumLiterals.next(), compareReferences);
      }
      if (compareReferences) {
         // Compare implements
         TestCase.assertEquals(dsEnum.getImplements().size(), dbcEnum.getImplements().size());
         Iterator<IDSInterface> dsImplements = dsEnum.getImplements().iterator();
         Iterator<DbcInterface> dbcImplements = dbcEnum.getImplements().iterator();
         while (dsImplements.hasNext() && dbcImplements.hasNext()) {
            compareInterface(dsImplements.next(), dbcImplements.next(), false);
         }
         // Compare implements full names
         TestCase.assertEquals(dsEnum.getImplementsFullnames().size(), dbcEnum.getImplementsFullNames().size());
         Iterator<String> dsImplementsNames = dsEnum.getImplementsFullnames().iterator();
         Iterator<String> dbcImplementsNames = dbcEnum.getImplementsFullNames().iterator();
         while (dsImplementsNames.hasNext() && dbcImplementsNames.hasNext()) {
            TestCase.assertEquals(dsImplementsNames.next(), dbcImplementsNames.next());
         }
         // Compare contained type invariants
         TestCase.assertEquals(dsEnum.getMethods().size(), dbcEnum.getMethods().size());
         Iterator<IDSInvariant> dsTypeInvariants = dsEnum.getInvariants().iterator();
         Iterator<DbcInvariant> dbcInvariants = dbcEnum.getInvariants().iterator();
         while (dsTypeInvariants.hasNext() && dbcInvariants.hasNext()) {
            compareInvariant(dsTypeInvariants.next(), dbcInvariants.next());
         }
      }
      // Compare parent
      compareTypeParent(dsEnum, dbcEnum);
   }

   /**
    * Compares the data source interface with the model interface.
    * @param dsInterface The expected data source interface.
    * @param dbcInterface The current model interface.
    * @throws DSException Occurred Exception
    */   
   public static void compareInterface(IDSInterface dsInterface, 
                                       DbcInterface dbcInterface, 
                                       boolean compareReferences) throws DSException {
      TestCase.assertNotNull(dsInterface);
      TestCase.assertNotNull(dbcInterface);
      TestCase.assertEquals(dsInterface.isStatic(), dbcInterface.isStatic());
      TestCase.assertEquals(dsInterface.getName(), dbcInterface.getName());
      compareProvable(dsInterface, dbcInterface);
      compareVisibility(dsInterface.getVisibility(), dbcInterface.getVisibility());
      // Compare axioms
      compareAxioms(dsInterface.getAxioms(), dbcInterface.getAxioms(), compareReferences);
      // Compare inner types
      if (compareReferences) {
         compareTypes(dsInterface.getInnerClasses(), dsInterface.getInnerEnums(), dsInterface.getInnerInterfaces(), dbcInterface.getTypes());
      }
      // Compare contained attributes
      TestCase.assertEquals(dsInterface.getAttributes().size(), dbcInterface.getAttributes().size());
      Iterator<IDSAttribute> dsAttributes = dsInterface.getAttributes().iterator();
      Iterator<DbcAttribute> dbcAttributes = dbcInterface.getAttributes().iterator();
      while (dsAttributes.hasNext() && dbcAttributes.hasNext()) {
         compareAttribute(dsAttributes.next(), dbcAttributes.next(), compareReferences);
      }
      if (compareReferences) {
         // Compare contained methods
         TestCase.assertEquals(dsInterface.getMethods().size(), dbcInterface.getMethods().size());
         Iterator<IDSMethod> dsMethods = dsInterface.getMethods().iterator();
         Iterator<DbcMethod> dbcMethods = dbcInterface.getMethods().iterator();
         while (dsMethods.hasNext() && dbcMethods.hasNext()) {
            compareMethod(dsMethods.next(), dbcMethods.next(), true);
         }
         // Compare extends
         TestCase.assertEquals(dsInterface.getExtends().size(), dbcInterface.getExtends().size());
         Iterator<IDSInterface> dsExtends = dsInterface.getExtends().iterator();
         Iterator<DbcInterface> dbcExtends = dbcInterface.getExtends().iterator();
         while (dsExtends.hasNext() && dbcExtends.hasNext()) {
            compareInterface(dsExtends.next(), dbcExtends.next(), false);
         }
         // Compare extends full names
         TestCase.assertEquals(dsInterface.getExtendsFullnames().size(), dbcInterface.getExtendsFullNames().size());
         Iterator<String> dsExtendsNames = dsInterface.getExtendsFullnames().iterator();
         Iterator<String> dbcExtendsNames = dbcInterface.getExtendsFullNames().iterator();
         while (dsExtendsNames.hasNext() && dbcExtendsNames.hasNext()) {
            TestCase.assertEquals(dsExtendsNames.next(), dbcExtendsNames.next());
         }
         // Compare contained type invariants
         TestCase.assertEquals(dsInterface.getMethods().size(), dbcInterface.getMethods().size());
         Iterator<IDSInvariant> dsTypeInvariants = dsInterface.getInvariants().iterator();
         Iterator<DbcInvariant> dbcInvariants = dbcInterface.getInvariants().iterator();
         while (dsTypeInvariants.hasNext() && dbcInvariants.hasNext()) {
            compareInvariant(dsTypeInvariants.next(), dbcInvariants.next());
         }
      }
      // Compare parent
      compareTypeParent(dsInterface, dbcInterface);
   }

   /**
    * Compares the data source class with the model class.
    * @param dsClass The expected data source class.
    * @param dbcClass The current model class.
    * @param compareReferences Compare references?
    * @throws DSException Occurred Exception
    */
   public static void compareClass(IDSClass dsClass, 
                                   DbcClass dbcClass, 
                                   boolean compareReferences) throws DSException {
      TestCase.assertNotNull(dsClass);
      TestCase.assertNotNull(dbcClass);
      TestCase.assertEquals(dsClass.isAnonymous(), dbcClass.isAnonymous());
      TestCase.assertEquals(dsClass.isAbstract(), dbcClass.isAbstract());
      TestCase.assertEquals(dsClass.isFinal(), dbcClass.isFinal());
      TestCase.assertEquals(dsClass.isStatic(), dbcClass.isStatic());
      compareProvable(dsClass, dbcClass);
      compareClassName(dsClass, dbcClass);
      compareVisibility(dsClass.getVisibility(), dbcClass.getVisibility());
      // Compare axioms
      compareAxioms(dsClass.getAxioms(), dbcClass.getAxioms(), compareReferences);
      // Compare inner types
      if (compareReferences) {
         compareTypes(dsClass.getInnerClasses(), dsClass.getInnerEnums(), dsClass.getInnerInterfaces(), dbcClass.getTypes());
      }
      // Compare contained attributes
      TestCase.assertEquals(dsClass.getName(), dsClass.getAttributes().size(), dbcClass.getAttributes().size());
      Iterator<IDSAttribute> dsAttributes = dsClass.getAttributes().iterator();
      Iterator<DbcAttribute> dbcAttributes = dbcClass.getAttributes().iterator();
      while (dsAttributes.hasNext() && dbcAttributes.hasNext()) {
         compareAttribute(dsAttributes.next(), dbcAttributes.next(), compareReferences);
      }
      if (compareReferences) {
         // Compare contained methods
         TestCase.assertEquals(dsClass.getMethods().size(), dbcClass.getMethods().size());
         Iterator<IDSMethod> dsMethods = dsClass.getMethods().iterator();
         Iterator<DbcMethod> dbcMethods = dbcClass.getMethods().iterator();
         while (dsMethods.hasNext() && dbcMethods.hasNext()) {
            compareMethod(dsMethods.next(), dbcMethods.next(), true);
         }
         // Compare contained constructors
         TestCase.assertEquals(dsClass.getConstructors().size(), dbcClass.getConstructors().size());
         Iterator<IDSConstructor> dsConstructors = dsClass.getConstructors().iterator();
         Iterator<DbcConstructor> dbcConstructors = dbcClass.getConstructors().iterator();
         while (dsConstructors.hasNext() && dbcConstructors.hasNext()) {
            compareConstructor(dsConstructors.next(), dbcConstructors.next(), true);
         }
         // Compare extends
         TestCase.assertEquals(dsClass.getExtends().size(), dbcClass.getExtends().size());
         Iterator<IDSClass> dsExtends = dsClass.getExtends().iterator();
         Iterator<DbcClass> dbcExtends = dbcClass.getExtends().iterator();
         while (dsExtends.hasNext() && dbcExtends.hasNext()) {
            compareClass(dsExtends.next(), dbcExtends.next(), false);
         }
         // Compare extends full names
         TestCase.assertEquals(dsClass.getExtendsFullnames().size(), dbcClass.getExtendsFullNames().size());
         Iterator<String> dsExtendsNames = dsClass.getExtendsFullnames().iterator();
         Iterator<String> dbcExtendsNames = dbcClass.getExtendsFullNames().iterator();
         while (dsExtendsNames.hasNext() && dbcExtendsNames.hasNext()) {
            TestCase.assertEquals(dsExtendsNames.next(), dbcExtendsNames.next());
         }
         // Compare implements
         TestCase.assertEquals(dsClass.getImplements().size(), dbcClass.getImplements().size());
         Iterator<IDSInterface> dsImplements = dsClass.getImplements().iterator();
         Iterator<DbcInterface> dbcImplements = dbcClass.getImplements().iterator();
         while (dsImplements.hasNext() && dbcImplements.hasNext()) {
            compareInterface(dsImplements.next(), dbcImplements.next(), false);
         }
         // Compare implements full names
         TestCase.assertEquals(dsClass.getImplementsFullnames().size(), dbcClass.getImplementsFullNames().size());
         Iterator<String> dsImplementsNames = dsClass.getImplementsFullnames().iterator();
         Iterator<String> dbcImplementsNames = dbcClass.getImplementsFullNames().iterator();
         while (dsImplementsNames.hasNext() && dbcImplementsNames.hasNext()) {
            TestCase.assertEquals(dsImplementsNames.next(), dbcImplementsNames.next());
         }
         // Compare contained type invariants
         TestCase.assertEquals(dsClass.getMethods().size(), dbcClass.getMethods().size());
         Iterator<IDSInvariant> dsTypeInvariants = dsClass.getInvariants().iterator();
         Iterator<DbcInvariant> dbcInvariants = dbcClass.getInvariants().iterator();
         while (dsTypeInvariants.hasNext() && dbcInvariants.hasNext()) {
            compareInvariant(dsTypeInvariants.next(), dbcInvariants.next());
         }
      }
      // Compare parent
      compareTypeParent(dsClass, dbcClass);
   }

   /**
    * Compares the provables.
    * @param dsProvable The data source provable.
    * @param dbcProvable The dbc provable.
    * @throws DSException Occurred Exception.
    */   
   public static void compareProvable(IDSProvable dsProvable, IDbCProvable dbcProvable) throws DSException {
      TestCase.assertNotNull(dsProvable);
      TestCase.assertNotNull(dbcProvable);
      TestCase.assertEquals(dsProvable.getObligations().size(), dbcProvable.getProofObligations().size());
      Iterator<String> dsIter = dsProvable.getObligations().iterator();
      Iterator<DbcProofObligation> dbcIter = dbcProvable.getProofObligations().iterator();
      while (dsIter.hasNext() && dbcIter.hasNext()) {
         String dsNext = dsIter.next();
         DbcProofObligation dbcNext = dbcIter.next();
         TestCase.assertEquals(dsNext, dbcNext.getObligation());
      }
      TestCase.assertFalse(dsIter.hasNext());
      TestCase.assertFalse(dbcIter.hasNext());
   }


   /**
    * Compares the parent of the given operations.
    * @param dsOperation The data source operation.
    * @param dbcOperation The dbc operation.
    * @throws DSException Occurred Exception.
    */
   public static void compareOperationParent(IDSOperation dsOperation, AbstractDbcOperation dbcOperation) throws DSException {
      if (dsOperation.getParent() instanceof IDSClass) {
         TestCase.assertTrue(dbcOperation.eContainer() instanceof DbcClass);
         compareClass((IDSClass)dsOperation.getParent(), (DbcClass)dbcOperation.eContainer(), false);
      }
      else if (dsOperation.getParent() instanceof IDSInterface) {
         TestCase.assertTrue(dbcOperation.eContainer() instanceof DbcInterface);
         compareInterface((IDSInterface)dsOperation.getParent(), (DbcInterface)dbcOperation.eContainer(), false);
      }
      else if (dsOperation.getParent() instanceof IDSEnum) {
         TestCase.assertTrue(dbcOperation.eContainer() instanceof DbcEnum);
         compareEnum((IDSEnum)dsOperation.getParent(), (DbcEnum)dbcOperation.eContainer(), false);
      }
      else {
         fail("Data source type \"" + dsOperation + "\" has no parent.");
      }
   }

   /**
    * Compares the parent of the given type.
    * @param dsType The data source type.
    * @param dbcType The model type.
    * @throws DSException Occurred Exception.
    */
   public static void compareTypeParent(IDSType dsType, AbstractDbcType dbcType) throws DSException {
      if (dsType.getParentContainer() != null) {
         TestCase.assertNull(dsType.getParentType());
         if (dsType.getParentContainer() instanceof IDSPackage) {
            TestCase.assertTrue(dbcType.eContainer() instanceof DbcPackage);
            comparePackage((IDSPackage)dsType.getParentContainer(), (DbcPackage)dbcType.eContainer(), false);
         }
         else if (dsType.getParentContainer() instanceof IDSConnection) {
            TestCase.assertTrue(dbcType.eContainer() instanceof DbcModel);
         }
         else {
            fail("Unsupported type parent: " + dsType.getParentContainer());
         }
      }
      else if (dsType.getParentType() != null) {
         TestCase.assertNull(dsType.getParentContainer());
         if (dsType.getParentType() instanceof IDSClass) {
            TestCase.assertTrue(dbcType.eContainer() instanceof DbcClass);
            compareClass((IDSClass)dsType.getParentType(), (DbcClass)dbcType.eContainer(), false);
         }
         else if (dsType.getParentType() instanceof IDSInterface) {
            TestCase.assertTrue(dbcType.eContainer() instanceof DbcInterface);
            compareInterface((IDSInterface)dsType.getParentType(), (DbcInterface)dbcType.eContainer(), false);
         }
         else if (dsType.getParentType() instanceof IDSEnum) {
            TestCase.assertTrue(dbcType.eContainer() instanceof DbcEnum);
            compareEnum((IDSEnum)dsType.getParentType(), (DbcEnum)dbcType.eContainer(), false);
         }
         else {
            fail("Unsupported type parent: " + dsType.getParentType());
         }
      }
      else {
         fail("Data source type \"" + dsType + "\" has no parent.");
      }
   }

   /**
    * Compares the class names of the given classes.  
    * @param dsClass The expected class.
    * @param dbcClass The current class.
    * @throws DSException Occurred Exception
    */
   public static void compareClassName(IDSClass dsClass, DbcClass dbcClass) throws DSException {
      TestCase.assertEquals(dsClass.isAnonymous(), dbcClass.isAnonymous());
      if(!dsClass.isAnonymous()) {
         TestCase.assertEquals(dsClass.getName(), dbcClass.getName());
      }
   }

   /**
    * Compares the data source visibility with the model visibility.
    * @param dsVisibility The expected data source visibility.
    * @param dbcVisibility The current model visibility.
    */
   public static void compareVisibility(DSVisibility dsVisibility, DbcVisibility dbcVisibility) {
      if (dsVisibility != null && dbcVisibility != null) {
         switch (dsVisibility) {
            case PRIVATE : TestCase.assertEquals(DbcVisibility.PRIVATE, dbcVisibility);
                           break;
            case PROTECTED : TestCase.assertEquals(DbcVisibility.PROTECTED, dbcVisibility);
                             break;
            case PUBLIC : TestCase.assertEquals(DbcVisibility.PUBLIC, dbcVisibility);
                          break;
            default : TestCase.assertEquals(DbcVisibility.DEFAULT, dbcVisibility);
                      break;
         }
      }
      else {
         TestCase.assertNull(dsVisibility);
         TestCase.assertNull(dbcVisibility);
      }
   }

   /**
    * Compares the data source package with the model package.
    * @param dsPackage The expected data source package.
    * @param dbcPackage The current model package.
    * @param compareChildren Indicates that child packages are compared or not.
    * @throws DSException Occurred Exception
    */
   public static void comparePackage(IDSPackage dsPackage, DbcPackage dbcPackage, boolean compareChildren) throws DSException {
      TestCase.assertNotNull(dsPackage);
      TestCase.assertNotNull(dbcPackage);
      TestCase.assertEquals(dsPackage.getName(), dbcPackage.getName());
      // Compare contained packages
      if (compareChildren) {
         TestCase.assertEquals(dsPackage.getPackages().size(), dbcPackage.getPackages().size());
         Iterator<IDSPackage> dsPackages = dsPackage.getPackages().iterator();
         Iterator<DbcPackage> dbcPackages = dbcPackage.getPackages().iterator();
         while (dsPackages.hasNext() && dbcPackages.hasNext()) {
            comparePackage(dsPackages.next(), dbcPackages.next(), true);
         }
      }
      // Compare parent
      TestCase.assertFalse(dsPackage == dsPackage.getParent());
      if (dsPackage.getParent() instanceof IDSPackage) {
         TestCase.assertTrue(dbcPackage.eContainer() instanceof DbcPackage);
         comparePackage((IDSPackage)dsPackage.getParent(), (DbcPackage)dbcPackage.eContainer(), false);
      }
      else if (dsPackage.getParent() instanceof IDSConnection) {
         TestCase.assertTrue(((IDSConnection)dsPackage.getParent()).getPackages().contains(dsPackage));
      }
      else {
         TestCase.fail("Unsupported parent \"" + dsPackage.getParent() + "\".");
      }
      // Compare contained types
      if (compareChildren) {
         compareTypes(dsPackage.getClasses(), dsPackage.getEnums(), dsPackage.getInterfaces(), dbcPackage.getTypes());
      }
   }

   /**
    * Creates the default connection settings for a data source connection
    * of the given {@link IDSDriver} and the {@link ISelection}.
    * @param driver The {@link IDSDriver}.
    * @param selection The {@link ISelection}.
    * @return The created default connection settings.
    */
   public static Map<String, Object> createDefaultSettings(IDSDriver driver, ISelection selection) {
      TestCase.assertNotNull(driver);
      Map<String, Object> result = new HashMap<String, Object>();
      List<IDSConnectionSetting> settings = driver.getConnectionSettings();
      for (IDSConnectionSetting setting : settings) {
         result.put(setting.getKey(), setting.getInitialValue(selection));
      }
      return result;
   }
   
   /**
    * Compares the given {@link IDSConnection}s.
    * @param expected The expected values.
    * @param current The current values.
    * @throws DSException Occurred Exception
    */
   public static void compareConnection(IDSConnection expected,
                                        IDSConnection current) throws DSException {
      // Compare packages
      comparePackages(expected.getPackages(), current.getPackages());
      // Compare classes
      compareClasses("IDSConnection", expected.getClasses(), current.getClasses());
      // Compare interfaces
      compareInterfaces(expected.getInterfaces(), current.getInterfaces());
      // Compare enumerations
      compareEnums(expected.getEnums(), current.getEnums());
   }

   /**
    * Compares the given enumeration {@link List}s.
    * @param expected The expected values.
    * @param current The current values.
    * @throws DSException Occurred Exception
    */
   public static void compareEnums(List<IDSEnum> expected, List<IDSEnum> current) throws DSException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.size(), current.size());
      Iterator<IDSEnum> exClassIter = expected.iterator();
      Iterator<IDSEnum> curClassIter = current.iterator();
      while (exClassIter.hasNext() && curClassIter.hasNext()) {
         compareEnum(exClassIter.next(), curClassIter.next(), true);
      }
      TestCase.assertFalse(exClassIter.hasNext());
      TestCase.assertFalse(curClassIter.hasNext());
   }

   /**
    * Compares the given interface {@link List}s.
    * @param expected The expected values.
    * @param current The current values.
    * @throws DSException Occurred Exception
    */
   public static void compareInterfaces(List<IDSInterface> expected, List<IDSInterface> current) throws DSException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.size(), current.size());
      Iterator<IDSInterface> exClassIter = expected.iterator();
      Iterator<IDSInterface> curClassIter = current.iterator();
      while (exClassIter.hasNext() && curClassIter.hasNext()) {
         compareInterface(exClassIter.next(), curClassIter.next(), true);
      }
      TestCase.assertFalse(exClassIter.hasNext());
      TestCase.assertFalse(curClassIter.hasNext());
   }

   /**
    * Compares the given string {@link List}s.
    * @param message The message to show if an assertion fails.
    * @param expected The expected values.
    * @param current The current values.
    */
   public static void compareStrings(String message, List<String> expected, List<String> current) {
      TestCase.assertNotNull(message, expected);
      TestCase.assertNotNull(message, current);
      TestCase.assertEquals(message + "expected: " + CollectionUtil.toString(expected) + " but is currently: " + CollectionUtil.toString(current), expected.size(), current.size());
      Iterator<String> exClassIter = expected.iterator();
      Iterator<String> curClassIter = current.iterator();
      while (exClassIter.hasNext() && curClassIter.hasNext()) {
         TestCase.assertEquals(exClassIter.next(), curClassIter.next());
      }
      TestCase.assertFalse(message, exClassIter.hasNext());
      TestCase.assertFalse(message, curClassIter.hasNext());
   }   
   
   /**
    * Compares the given class {@link List}s.
    * @param message The message to show if an assertion fails.
    * @param expected The expected values.
    * @param current The current values.
    * @throws DSException Occurred Exception
    */
   public static void compareClasses(String message, List<IDSClass> expected, List<IDSClass> current) throws DSException {
      TestCase.assertNotNull(message, expected);
      TestCase.assertNotNull(message, current);
      TestCase.assertEquals(message, expected.size(), current.size());
      Iterator<IDSClass> exClassIter = expected.iterator();
      Iterator<IDSClass> curClassIter = current.iterator();
      while (exClassIter.hasNext() && curClassIter.hasNext()) {
         compareClass(exClassIter.next(), curClassIter.next(), true);
      }
      TestCase.assertFalse(message, exClassIter.hasNext());
      TestCase.assertFalse(message, curClassIter.hasNext());
   }
   
   /**
    * Compares the given {@link IDSInterface}s.
    * @param expected The expected values.
    * @param current The current values.
    * @param compareReferences Compare references?
    * @throws DSException Occurred Exception
    */
   public static void compareInterface(IDSInterface expected, IDSInterface current, boolean compareReferences) throws DSException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.isStatic(), current.isStatic());
      TestCase.assertEquals(expected.getName(), current.getName());
      TestCase.assertEquals(expected.getVisibility(), current.getVisibility());
      if (compareReferences) {
         compareMethods(expected.getMethods(), current.getMethods());
      }
      compareAttributes(expected.getAttributes(), current.getAttributes(), compareReferences);
      if (compareReferences) {
         compareClasses(current.getName(), expected.getInnerClasses(), current.getInnerClasses());
         compareInterfaces(expected.getInnerInterfaces(), current.getInnerInterfaces());
         compareEnums(expected.getInnerEnums(), current.getInnerEnums());
         compareInvariants(expected.getInvariants(), current.getInvariants());
      }
      compareStrings(expected.getName(), expected.getExtendsFullnames(), current.getExtendsFullnames());
      compareInterfaces(expected.getExtends(), current.getExtends());
      compareProofObligations(expected.getName(), expected.getObligations(), current.getObligations());
      compareTypeParent(expected, current);
   }
   
   /**
    * Compares the given {@link IDSClass}s.
    * @param expected The expected values.
    * @param current The current values.
    * @param compareReferences Compare references?
    * @throws DSException Occurred Exception
    */
   public static void compareClass(IDSClass expected, IDSClass current, boolean compareReferences) throws DSException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.getName(), expected.isAnonymous(), current.isAnonymous());
      TestCase.assertEquals(expected.getName(), expected.isAbstract(), current.isAbstract());
      TestCase.assertEquals(expected.getName(), expected.isFinal(), current.isFinal());
      TestCase.assertEquals(expected.getName(), expected.isStatic(), current.isStatic());
      compareClassName(expected, current);
      TestCase.assertEquals(expected.getName(), expected.getVisibility(), current.getVisibility());
      if (compareReferences) {
         compareConstructors(expected.getConstructors(), current.getConstructors());
         compareMethods(expected.getMethods(), current.getMethods());
      }
      compareAttributes(expected.getAttributes(), current.getAttributes(), compareReferences);
      if (compareReferences) {
         compareClasses(current.getName(), expected.getInnerClasses(), current.getInnerClasses());
         compareInterfaces(expected.getInnerInterfaces(), current.getInnerInterfaces());
         compareEnums(expected.getInnerEnums(), current.getInnerEnums());
      }
      compareStrings(expected.getName(), expected.getExtendsFullnames(), current.getExtendsFullnames());
      compareStrings(expected.getName(), expected.getImplementsFullnames(), current.getImplementsFullnames());
      if (compareReferences) {
         compareClasses(expected.getName(), expected.getExtends(), current.getExtends());
         compareInterfaces(expected.getImplements(), current.getImplements());
         compareInvariants(expected.getInvariants(), current.getInvariants());
         compareAxioms(expected.getAxioms(), current.getAxioms());
      }
      compareProofObligations(expected.getName(), expected.getObligations(), current.getObligations());
      compareTypeParent(expected, current);
   }

   /**
    * Compares the parent of the given {@link IDSOperation}s.
    * @param expected The expected type.
    * @param current The current type.
    * @throws DSException Occurred Exception.
    */   
   public static void compareOperationParent(IDSOperation expected, IDSOperation current) throws DSException {
      if (expected.getParent() instanceof IDSClass) {
         TestCase.assertTrue(current.getParent() instanceof IDSClass);
         compareClass((IDSClass)expected.getParent(), (IDSClass)current.getParent(), false);
      }
      else if (expected.getParent() instanceof IDSInterface) {
         TestCase.assertTrue(current.getParent() instanceof IDSInterface);
         compareInterface((IDSInterface)expected.getParent(), (IDSInterface)current.getParent(), false);
      }
      else if (expected.getParent() instanceof IDSEnum) {
         TestCase.assertTrue(current.getParent() instanceof IDSEnum);
         compareEnum((IDSEnum)expected.getParent(), (IDSEnum)current.getParent(), false);
      }
      else {
         TestCase.fail("Unsupported parent \"" + expected.getParent() + "\".");
      }
   }
   
   /**
    * Compares the parent of the given {@link IDSType}s.
    * @param expected The expected type.
    * @param current The current type.
    * @throws DSException Occurred Exception.
    */
   public static void compareTypeParent(IDSType expected, IDSType current) throws DSException {
      if (expected.getParentContainer() != null) {
         TestCase.assertNull(expected.getParentType());
         if (expected.getParentContainer() instanceof IDSPackage) {
            TestCase.assertTrue(current.getParentContainer() instanceof IDSPackage);
            comparePackage((IDSPackage)expected.getParentContainer(), (IDSPackage)current.getParentContainer(), false);
         }
         else if (expected.getParentContainer() instanceof IDSConnection) {
            TestCase.assertTrue(current.getParentContainer() instanceof IDSConnection);
         }
         else{
            TestCase.fail("Unsupported parent \"" + expected.getParentContainer() + "\".");
         }
      }
      else if (expected.getParentType() != null) {
         TestCase.assertNull(expected.getParentContainer());
         if (expected.getParentType() instanceof IDSClass) {
            TestCase.assertTrue(current.getParentType() instanceof IDSClass);
            compareClass((IDSClass)expected.getParentType(), (IDSClass)current.getParentType(), false);
         }
         else if (expected.getParentType() instanceof IDSInterface) {
            TestCase.assertTrue(current.getParentType() instanceof IDSInterface);
            compareInterface((IDSInterface)expected.getParentType(), (IDSInterface)current.getParentType(), false);
         }
         else if (expected.getParentType() instanceof IDSEnum) {
            TestCase.assertTrue(current.getParentType() instanceof IDSEnum);
            compareEnum((IDSEnum)expected.getParentType(), (IDSEnum)current.getParentType(), false);
         }
         else{
            TestCase.fail("Unsupported parent \"" + expected.getParentType() + "\".");
         }
      }
      else {
         TestCase.fail("Type has no parent: " + expected);
      }
   }

   /**
    * Compares the class names of the given {@link IDSClass}es.
    * @param expected The expected {@link IDSClass}.
    * @param current The current {@link IDSClass}.
    * @throws DSException Occurred Exception
    */
   public static void compareClassName(IDSClass expected, IDSClass current) throws DSException {
      TestCase.assertEquals(expected.getName(), expected.isAnonymous(), current.isAnonymous());
      if (!expected.isAnonymous()) {
         TestCase.assertEquals(expected.getName(), current.getName());
      }
   }

   /**
    * Compares the given {@link IDSEnum}s.
    * @param expected The expected values.
    * @param current The current values.
    * @param compareReferences Compare references?
    * @throws DSException Occurred Exception
    */
   public static void compareEnum(IDSEnum expected, IDSEnum current, boolean compareReferences) throws DSException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.isStatic(), current.isStatic());
      TestCase.assertEquals(expected.getName(), current.getName());
      TestCase.assertEquals(expected.getVisibility(), current.getVisibility());
      if (compareReferences) {
         compareConstructors(expected.getConstructors(), current.getConstructors());
         compareMethods(expected.getMethods(), current.getMethods());
      }
      compareAttributes(expected.getAttributes(), current.getAttributes(), compareReferences);
      if (compareReferences) {
         compareClasses(current.getName(), expected.getInnerClasses(), current.getInnerClasses());
         compareInterfaces(expected.getInnerInterfaces(), current.getInnerInterfaces());
         compareEnums(expected.getInnerEnums(), current.getInnerEnums());
         compareInvariants(expected.getInvariants(), current.getInvariants());
      }
      compareEnumLiterals(expected.getLiterals(), current.getLiterals(), compareReferences);
      compareStrings(expected.getName(), expected.getImplementsFullnames(), current.getImplementsFullnames());
      if (compareReferences) {
         compareInterfaces(expected.getImplements(), current.getImplements());
      }
      compareProofObligations(expected.getName(), expected.getObligations(), current.getObligations());
      compareTypeParent(expected, current);
   }

   /**
    * Compares the given enumeration literal {@link List}s.
    * @param expected The expected values.
    * @param current The current values.
    * @param compareReferences Compare references?
    * @throws DSException Occurred Exception
    */ 
   public static void compareEnumLiterals(List<IDSEnumLiteral> expected, List<IDSEnumLiteral> current, boolean compareReferences) throws DSException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.size(), current.size());
      Iterator<IDSEnumLiteral> exClassIter = expected.iterator();
      Iterator<IDSEnumLiteral> curClassIter = current.iterator();
      while (exClassIter.hasNext() && curClassIter.hasNext()) {
         compareEnumLiteral(exClassIter.next(), curClassIter.next(), compareReferences);
      }
      TestCase.assertFalse(exClassIter.hasNext());
      TestCase.assertFalse(curClassIter.hasNext());
   }

   /**
    * Compares the given {@link IDSEnumLiteral}s.
    * @param expected The expected values.
    * @param current The current values.
    * @param compareReferences Compare references?
    * @throws DSException Occurred Exception
    */
   public static void compareEnumLiteral(IDSEnumLiteral expected, IDSEnumLiteral current, boolean compareReferences) throws DSException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.getName(), current.getName());
      if (compareReferences) {
         // Compare parent
         if (expected.getParent() instanceof IDSClass) {
            TestCase.assertTrue(current.getParent() instanceof IDSClass);
            compareClass((IDSClass)expected.getParent(), (IDSClass)current.getParent(), false);
         }
         else if (expected.getParent() instanceof IDSInterface) {
            TestCase.assertTrue(current.getParent() instanceof IDSInterface);
            compareInterface((IDSInterface)expected.getParent(), (IDSInterface)current.getParent(), false);
         }
         else if (expected.getParent() instanceof IDSEnum) {
            TestCase.assertTrue(current.getParent() instanceof IDSEnum);
            compareEnum((IDSEnum)expected.getParent(), (IDSEnum)current.getParent(), false);
         }
         else {
            TestCase.fail("Unsupported parent \"" + expected.getParent() + "\".");
         }
      }
   }

   /**
    * Compares the given proof obligation {@link List}s.
    * @param message The message to show.
    * @param expected The expected values.
    * @param current The current values.
    */
   public static void compareProofObligations(String message, List<String> expected, List<String> current) {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(message, expected.size(), current.size());
      Iterator<String> exClassIter = expected.iterator();
      Iterator<String> curClassIter = current.iterator();
      while (exClassIter.hasNext() && curClassIter.hasNext()) {
         TestCase.assertEquals(message, exClassIter.next(), curClassIter.next());
      }
      TestCase.assertFalse(exClassIter.hasNext());
      TestCase.assertFalse(curClassIter.hasNext());
   }
   
   /**
    * Compares the given invariants {@link List}s.
    * @param expected The expected values.
    * @param current The current values.
    * @throws DSException Occurred Exception
    */ 
   public static void compareInvariants(List<IDSInvariant> expected, List<IDSInvariant> current) throws DSException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.size(), current.size());
      Iterator<IDSInvariant> exClassIter = expected.iterator();
      Iterator<IDSInvariant> curClassIter = current.iterator();
      while (exClassIter.hasNext() && curClassIter.hasNext()) {
         compareInvariant(exClassIter.next(), curClassIter.next());
      }
      TestCase.assertFalse(exClassIter.hasNext());
      TestCase.assertFalse(curClassIter.hasNext());
   }

   /**
    * Compares the given {@link IDSInvariant}s.
    * @param expected The expected values.
    * @param current The current values.
    * @throws DSException Occurred Exception
    */   
   public static void compareInvariant(IDSInvariant expected, IDSInvariant current) throws DSException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.getName(), current.getName());
      TestCase.assertEquals(expected.getCondition(), current.getCondition());
      compareProofObligations(expected.getName(), expected.getObligations(), current.getObligations());
      // Compare parent
      if (expected.getParent() instanceof IDSClass) {
         TestCase.assertTrue(current.getParent() instanceof IDSClass);
         compareClass((IDSClass)expected.getParent(), (IDSClass)current.getParent(), false);
      }
      else if (expected.getParent() instanceof IDSInterface) {
         TestCase.assertTrue(current.getParent() instanceof IDSInterface);
         compareInterface((IDSInterface)expected.getParent(), (IDSInterface)current.getParent(), false);
      }
      else if (expected.getParent() instanceof IDSEnum) {
         TestCase.assertTrue(current.getParent() instanceof IDSEnum);
         compareEnum((IDSEnum)expected.getParent(), (IDSEnum)current.getParent(), false);
      }
      else {
         TestCase.fail("Unsupported parent \"" + expected.getParent() + "\".");
      }
   }

   /**
    * Compares the given attributes {@link List}s.
    * @param expected The expected values.
    * @param current The current values.
    * @param compareReferences Compare references?
    * @throws DSException Occurred Exception
    */ 
   public static void compareAttributes(List<IDSAttribute> expected, List<IDSAttribute> current, boolean compareReferences) throws DSException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.size(), current.size());
      Iterator<IDSAttribute> exClassIter = expected.iterator();
      Iterator<IDSAttribute> curClassIter = current.iterator();
      while (exClassIter.hasNext() && curClassIter.hasNext()) {
         compareAttribute(exClassIter.next(), curClassIter.next(), compareReferences);
      }
      TestCase.assertFalse(exClassIter.hasNext());
      TestCase.assertFalse(curClassIter.hasNext());
   }

   /**
    * Compares the given operation contract {@link List}s.
    * @param message The message to show.
    * @param expected The expected values.
    * @param current The current values.
    * @throws DSException Occurred Exception
    */    
   public static void compareOperationContracts(String message, List<IDSOperationContract> expected, List<IDSOperationContract> current) throws DSException {
      TestCase.assertNotNull(message, expected);
      TestCase.assertNotNull(message, current);
      TestCase.assertEquals(message, expected.size(), current.size());
      Iterator<IDSOperationContract> exClassIter = expected.iterator();
      Iterator<IDSOperationContract> curClassIter = current.iterator();
      while (exClassIter.hasNext() && curClassIter.hasNext()) {
         compareOperationContract(message, exClassIter.next(), curClassIter.next());
      }
      TestCase.assertFalse(message, exClassIter.hasNext());
      TestCase.assertFalse(message, curClassIter.hasNext());
   }

   /**
    * Compares the given {@link IDSAttribute}s.
    * @param expected The expected values.
    * @param current The current values.
    * @param compareReferences Compare references?
    * @throws DSException Occurred Exception
    */
   public static void compareAttribute(IDSAttribute expected, IDSAttribute current, boolean compareReferences) throws DSException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.getName(), expected.isFinal(), current.isFinal());
      TestCase.assertEquals(expected.getName(), expected.isStatic(), current.isStatic());
      TestCase.assertEquals(expected.getName(), current.getName());
      TestCase.assertEquals(expected.getName(), expected.getType(), current.getType());
      TestCase.assertEquals(expected.getName(), expected.getVisibility(), current.getVisibility());
      if (compareReferences) {
         // Compare parent
         if (expected.getParent() instanceof IDSClass) {
            TestCase.assertTrue(current.getParent() instanceof IDSClass);
            compareClass((IDSClass)expected.getParent(), (IDSClass)current.getParent(), false);
         }
         else if (expected.getParent() instanceof IDSInterface) {
            TestCase.assertTrue(current.getParent() instanceof IDSInterface);
            compareInterface((IDSInterface)expected.getParent(), (IDSInterface)current.getParent(), false);
         }
         else if (expected.getParent() instanceof IDSEnum) {
            TestCase.assertTrue(current.getParent() instanceof IDSEnum);
            compareEnum((IDSEnum)expected.getParent(), (IDSEnum)current.getParent(), false);
         }
         else {
            TestCase.fail("Unsupported parent \"" + expected.getParent() + "\".");
         }
      }
   }

   /**
    * Compares the given {@link IDSOperationContract}s.
    * @param message The message to show.
    * @param expected The expected values.
    * @param current The current values.
    * @throws DSException Occurred Exception
    */   
   public static void compareOperationContract(String message, IDSOperationContract expected, IDSOperationContract current) throws DSException {
      TestCase.assertNotNull(message, expected);
      TestCase.assertNotNull(message, current);
      TestCase.assertEquals(message, expected.getName(), current.getName());
      TestCase.assertEquals(message, expected.getPre(), current.getPre());
      TestCase.assertEquals(message, expected.getPost(), current.getPost());
      TestCase.assertEquals(message, expected.getModifies(), current.getModifies());
      TestCase.assertEquals(message, expected.getTermination(), current.getTermination());
      compareProofObligations(message + " :: " + expected.getName(), expected.getObligations(), current.getObligations());
      // Compare parent
      if (expected.getParent() instanceof IDSMethod) {
         TestCase.assertTrue(current.getParent() instanceof IDSMethod);
         compareMethod((IDSMethod)expected.getParent(), (IDSMethod)current.getParent(), false);
      }
      else if (expected.getParent() instanceof IDSConstructor) {
         TestCase.assertTrue(current.getParent() instanceof IDSConstructor);
         compareConstructor((IDSConstructor)expected.getParent(), (IDSConstructor)current.getParent(), false);
      }
      else {
         TestCase.fail("Unsupported parent \"" + expected.getParent() + "\".");
      }
   }
   
   /**
    * Compares the given method {@link List}s.
    * @param expected The expected values.
    * @param current The current values.
    * @throws DSException Occurred Exception
    */ 
   public static void compareMethods(List<IDSMethod> expected, List<IDSMethod> current) throws DSException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.size(), current.size());
      Iterator<IDSMethod> exClassIter = expected.iterator();
      Iterator<IDSMethod> curClassIter = current.iterator();
      while (exClassIter.hasNext() && curClassIter.hasNext()) {
         compareMethod(exClassIter.next(), curClassIter.next(), true);
      }
      TestCase.assertFalse(exClassIter.hasNext());
      TestCase.assertFalse(curClassIter.hasNext());
   }

   /**
    * Compares the given constructor {@link List}s.
    * @param expected The expected values.
    * @param current The current values.
    * @throws DSException Occurred Exception
    */   
   public static void compareConstructors(List<IDSConstructor> expected, List<IDSConstructor> current) throws DSException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.size(), current.size());
      Iterator<IDSConstructor> exClassIter = expected.iterator();
      Iterator<IDSConstructor> curClassIter = current.iterator();
      while (exClassIter.hasNext() && curClassIter.hasNext()) {
         compareConstructor(exClassIter.next(), curClassIter.next(), true);
      }
      TestCase.assertFalse(exClassIter.hasNext());
      TestCase.assertFalse(curClassIter.hasNext());
   }

   /**
    * Compares the given {@link IDSMethod}s.
    * @param expected The expected values.
    * @param current The current values.
    * @param compareReferences Compare references?
    * @throws DSException Occurred Exception
    */
   public static void compareMethod(IDSMethod expected, IDSMethod current, boolean compareReferences) throws DSException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.getSignature(), expected.isAbstract(), current.isAbstract());
      TestCase.assertEquals(expected.getSignature(), expected.isFinal(), current.isFinal());
      TestCase.assertEquals(expected.getSignature(), expected.isStatic(), current.isStatic());
      TestCase.assertEquals(expected.getSignature(), expected.getReturnType(), current.getReturnType());
      TestCase.assertEquals(expected.getSignature(), current.getSignature());
      TestCase.assertEquals(expected.getSignature(), expected.getVisibility(), current.getVisibility());
      if (compareReferences) {
         compareOperationContracts(expected.getSignature(), expected.getOperationContracts(), current.getOperationContracts());
      }
      compareProofObligations(expected.getSignature(), expected.getObligations(), current.getObligations());
      compareOperationParent(expected, current);
   }

   /**
    * Compares the given {@link IDSConstructor}s.
    * @param expected The expected values.
    * @param current The current values.
    * @param compareReferences Compare references?
    * @throws DSException Occurred Exception
    */   
   public static void compareConstructor(IDSConstructor expected, IDSConstructor current, boolean compareReferences) throws DSException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.isStatic(), current.isStatic());
      TestCase.assertEquals(expected.getSignature(), current.getSignature());
      TestCase.assertEquals(expected.getVisibility(), current.getVisibility());
      if (compareReferences) {
         compareOperationContracts(expected.getSignature(), expected.getOperationContracts(), current.getOperationContracts());
      }
      compareProofObligations(expected.getSignature(), expected.getObligations(), current.getObligations());
      compareOperationParent(expected, current);
   }

   /**
    * Compares the given package {@link List}s.
    * @param expected The expected values.
    * @param current The current values.
    * @throws DSException Occurred Exception
    */
   public static void comparePackages(List<IDSPackage> expected, List<IDSPackage> current) throws DSException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      // Compare packages
      TestCase.assertEquals(expected.size(), current.size());
      Iterator<IDSPackage> exPackageIter = expected.iterator();
      Iterator<IDSPackage> curPackageIter = current.iterator();
      while (exPackageIter.hasNext() && curPackageIter.hasNext()) {
         comparePackage(exPackageIter.next(), curPackageIter.next(), true);
      }
      TestCase.assertFalse(exPackageIter.hasNext());
      TestCase.assertFalse(curPackageIter.hasNext());
   }
   
   /**
    * Compares the given {@link IDSPackage}s.
    * @param expected The expected values.
    * @param current The current values.
    * @param compareReferences Compare references?
    * @throws DSException Occurred Exception
    */
   public static void comparePackage(IDSPackage expected, IDSPackage current, boolean compareReferences) throws DSException {
      TestCase.assertNotNull(expected);
      TestCase.assertNotNull(current);
      TestCase.assertEquals(expected.getName(), current.getName());
      if (compareReferences) {
         // Compare packages
         comparePackages(expected.getPackages(), current.getPackages());
         // Compare classes
         compareClasses(current.getName(), expected.getClasses(), current.getClasses());
         // Compare interfaces
         compareInterfaces(expected.getInterfaces(), current.getInterfaces());
         // Compare enums
         compareEnums(expected.getEnums(), current.getEnums());
      }
      // Compare parent
      if (expected.getParent() instanceof IDSPackage) {
         TestCase.assertTrue(current.getParent() instanceof IDSPackage);
         comparePackage((IDSPackage)expected.getParent(), (IDSPackage)current.getParent(), false);
      }
      else if (expected.getParent() instanceof IDSConnection) {
         TestCase.assertTrue(current.getParent() instanceof IDSConnection);
      }
      else {
         TestCase.fail("Unsupported parent \"" + expected.getParent() + "\".");
      }
   }
}