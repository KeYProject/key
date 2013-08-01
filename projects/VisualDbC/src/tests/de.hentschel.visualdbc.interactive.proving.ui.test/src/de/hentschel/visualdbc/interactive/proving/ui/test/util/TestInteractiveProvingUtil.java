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

package de.hentschel.visualdbc.interactive.proving.ui.test.util;

import static org.junit.Assert.assertSame;

import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;

import org.eclipse.emf.common.util.TreeIterator;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.swtbot.eclipse.gef.finder.widgets.SWTBotGefEditPart;
import org.eclipse.swtbot.eclipse.gef.finder.widgets.SWTBotGefEditor;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.key_project.util.test.util.TestUtilsUtil;

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
import de.hentschel.visualdbc.datasource.util.DataSourceIterator;
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
import de.hentschel.visualdbc.dbcmodel.DbcProperty;
import de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable;
import de.hentschel.visualdbc.dbcmodel.IDbCProvable;
import de.hentschel.visualdbc.generation.test.util.TestGenerationUtil;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDSFinder;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDbcFinder;
import de.hentschel.visualdbc.interactive.proving.ui.job.StartProofJob;
import de.hentschel.visualdbc.interactive.proving.ui.job.event.IStartProofJobListener;
import de.hentschel.visualdbc.interactive.proving.ui.job.event.StartProofJobEvent;
import de.hentschel.visualdbc.interactive.proving.ui.util.FinderUtil;

/**
 * Provides static methods that make testing easier.
 * @author Martin Hentschel
 */
public final class TestInteractiveProvingUtil {
   /**
    * Forbid instances.
    */
   private TestInteractiveProvingUtil() {
   }
   
   /**
    * Uses the {@link IDbcFinder} to search every element in the connection.
    * @param connection The {@link IDSConnection} that contains the elements to search.
    * @param finder The {@link IDbcFinder} to use.
    * @throws DSException Occurred Exception.
    */
   public static void findAllElements(IDSConnection connection, final IDbcFinder finder) throws DSException {
      DataSourceIterator iter = new DataSourceIterator() {
         @Override
         protected void workOnPackage(IDSPackage instance) throws DSException {
            findPackage(finder, instance);
         }

         @Override
         protected void workOnClass(IDSClass instance) throws DSException {
            findClass(finder, instance);
         }

         @Override
         protected void workOnInterface(IDSInterface instance) throws DSException {
            findInterface(finder, instance);
         }

         @Override
         protected void workOnEnum(IDSEnum instance) throws DSException {
            findEnum(finder, instance);
         }

         @Override
         protected void workOnMethod(IDSMethod instance) throws DSException {
            findMethod(finder, instance);
         }

         @Override
         protected void workOnConstructor(IDSConstructor instance) throws DSException {
            findConstructor(finder, instance);
         }

         @Override
         protected void workOnOperationContract(IDSOperationContract instance) throws DSException {
            findOperationContract(finder, instance);
         }

         @Override
         protected void workOnInvariant(IDSInvariant instance) throws DSException {
            findInvariant(finder, instance);
         }

         @Override
         protected void workOnAxiom(IDSAxiom instance) throws DSException {
            findAxiom(finder, instance);
         }

         @Override
         protected void workOnAxiomContract(IDSAxiomContract instance) throws DSException {
            findAxiomContract(finder, instance);
         }

         @Override
         protected void workOnAttribute(IDSAttribute instance) throws DSException {
            findAttribute(finder, instance);
         }

         @Override
         protected void workOnEnumLiteral(IDSEnumLiteral instance) throws DSException {
            findEnumLiteral(finder, instance);
         }
      };
      iter.iterateOverConnection(connection);
   }

   /**
    * Uses the {@link IDbcFinder} to find the equal element for the given data source instance.
    * @param finder The {@link IDbcFinder} to use.
    * @param toSearch The data source element to search and to compare.
    * @throws DSException Occurred Exception.
    */   
   public static void findPackage(IDbcFinder finder, IDSPackage toSearch) throws DSException {
      DbcPackage found = finder.findPackage(toSearch);
      TestGenerationUtil.comparePackage(toSearch, found, true);
   }

   /**
    * Uses the {@link IDbcFinder} to find the equal element for the given data source instance.
    * @param finder The {@link IDbcFinder} to use.
    * @param toSearch The data source element to search and to compare.
    * @throws DSException Occurred Exception.
    */   
   public static void findClass(IDbcFinder finder, IDSClass toSearch) throws DSException {
      if (toSearch.isAnonymous()) {
         try {
            finder.findClass(toSearch);
            TestCase.fail();
         }
         catch (DSException e) {
            TestCase.assertEquals("Anonymous classes like \"" + toSearch.getName() + "\" are not supported.", e.getMessage());
         }
      }
      else {
         DbcClass found = finder.findClass(toSearch);
         TestGenerationUtil.compareClass(toSearch, found, true);
         IDbCProvable provable = finder.findProvable(toSearch);
         assertSame(found, provable);
         IDbCProofReferencable proofReferencable = finder.findProofReferencable(toSearch);
         assertSame(found, proofReferencable);      
      }
   }

   /**
    * Uses the {@link IDbcFinder} to find the equal element for the given data source instance.
    * @param finder The {@link IDbcFinder} to use.
    * @param toSearch The data source element to search and to compare.
    * @throws DSException Occurred Exception.
    */   
   public static void findInterface(IDbcFinder finder, IDSInterface toSearch) throws DSException {
      DbcInterface found = finder.findInterface(toSearch);
      TestGenerationUtil.compareInterface(toSearch, found, true);
      IDbCProvable provable = finder.findProvable(toSearch);
      assertSame(found, provable);      
      IDbCProofReferencable proofReferencable = finder.findProofReferencable(toSearch);
      assertSame(found, proofReferencable);      
   }

   /**
    * Uses the {@link IDbcFinder} to find the equal element for the given data source instance.
    * @param finder The {@link IDbcFinder} to use.
    * @param toSearch The data source element to search and to compare.
    * @throws DSException Occurred Exception.
    */   
   public static void findEnum(IDbcFinder finder, IDSEnum toSearch) throws DSException {
      DbcEnum found = finder.findEnum(toSearch);
      TestGenerationUtil.compareEnum(toSearch, found, true);
      IDbCProvable provable = finder.findProvable(toSearch);
      assertSame(found, provable);      
      IDbCProofReferencable proofReferencable = finder.findProofReferencable(toSearch);
      assertSame(found, proofReferencable);      
   }

   /**
    * Uses the {@link IDbcFinder} to find the equal element for the given data source instance.
    * @param finder The {@link IDbcFinder} to use.
    * @param toSearch The data source element to search and to compare.
    * @throws DSException Occurred Exception.
    */   
   public static void findMethod(IDbcFinder finder, IDSMethod toSearch) throws DSException {
      DbcMethod found = finder.findMethod(toSearch);
      TestGenerationUtil.compareMethod(toSearch, found, true);
      IDbCProvable provable = finder.findProvable(toSearch);
      assertSame(found, provable);      
      IDbCProofReferencable proofReferencable = finder.findProofReferencable(toSearch);
      assertSame(found, proofReferencable);      
   }

   /**
    * Uses the {@link IDbcFinder} to find the equal element for the given data source instance.
    * @param finder The {@link IDbcFinder} to use.
    * @param toSearch The data source element to search and to compare.
    * @throws DSException Occurred Exception.
    */   
   public static void findConstructor(IDbcFinder finder, IDSConstructor toSearch) throws DSException {
      DbcConstructor found = finder.findConstructor(toSearch);
      TestGenerationUtil.compareConstructor(toSearch, found, true);
      IDbCProvable provable = finder.findProvable(toSearch);
      assertSame(found, provable);      
      IDbCProofReferencable proofReferencable = finder.findProofReferencable(toSearch);
      assertSame(found, proofReferencable);      
   }

   /**
    * Uses the {@link IDbcFinder} to find the equal element for the given data source instance.
    * @param finder The {@link IDbcFinder} to use.
    * @param toSearch The data source element to search and to compare.
    * @throws DSException Occurred Exception.
    */
   public static void findOperationContract(IDbcFinder finder, IDSOperationContract toSearch) throws DSException {
      DbcOperationContract found = finder.findOperationContract(toSearch);
      TestGenerationUtil.compareOperationContract(toSearch, found);
      IDbCProvable provable = finder.findProvable(toSearch);
      assertSame(found, provable);      
      IDbCProofReferencable proofReferencable = finder.findProofReferencable(toSearch);
      assertSame(found, proofReferencable);      
   }

   /**
    * Uses the {@link IDbcFinder} to find the equal element for the given data source instance.
    * @param finder The {@link IDbcFinder} to use.
    * @param toSearch The data source element to search and to compare.
    * @throws DSException Occurred Exception.
    */   
   public static void findInvariant(IDbcFinder finder, IDSInvariant toSearch) throws DSException {
      DbcInvariant found = finder.findInvariant(toSearch);
      TestGenerationUtil.compareInvariant(toSearch, found);
      IDbCProofReferencable proofReferencable = finder.findProofReferencable(toSearch);
      assertSame(found, proofReferencable);      
   }

   /**
    * Uses the {@link IDbcFinder} to find the equal element for the given data source instance.
    * @param finder The {@link IDbcFinder} to use.
    * @param toSearch The data source element to search and to compare.
    * @throws DSException Occurred Exception.
    */   
   public static void findAttribute(IDbcFinder finder, IDSAttribute toSearch) throws DSException {
      DbcAttribute found = finder.findAttribute(toSearch);
      TestGenerationUtil.compareAttribute(toSearch, found, true);
      IDbCProofReferencable proofReferencable = finder.findProofReferencable(toSearch);
      assertSame(found, proofReferencable);      
   }

   /**
    * Uses the {@link IDbcFinder} to find the equal element for the given data source instance.
    * @param finder The {@link IDbcFinder} to use.
    * @param toSearch The data source element to search and to compare.
    * @throws DSException Occurred Exception.
    */   
   public static void findEnumLiteral(IDbcFinder finder, IDSEnumLiteral toSearch) throws DSException {
      DbcEnumLiteral found = finder.findEnumLiteral(toSearch);
      TestGenerationUtil.compareEnumLiteral(toSearch, found, true);
      IDbCProofReferencable proofReferencable = finder.findProofReferencable(toSearch);
      assertSame(found, proofReferencable);      
   }

   /**
    * Uses the {@link IDbcFinder} to find the equal element for the given data source instance.
    * @param finder The {@link IDbcFinder} to use.
    * @param toSearch The data source element to search and to compare.
    * @throws DSException Occurred Exception.
    */   
   public static void findAxiom(IDbcFinder finder, IDSAxiom toSearch) throws DSException {
      DbcAxiom found = finder.findAxiom(toSearch);
      TestGenerationUtil.compareAxiom(toSearch, found, true);
      IDbCProofReferencable proofReferencable = finder.findProofReferencable(toSearch);
      assertSame(found, proofReferencable);      
   }

   /**
    * Uses the {@link IDbcFinder} to find the equal element for the given data source instance.
    * @param finder The {@link IDbcFinder} to use.
    * @param toSearch The data source element to search and to compare.
    * @throws DSException Occurred Exception.
    */   
   public static void findAxiomContract(IDbcFinder finder, IDSAxiomContract toSearch) throws DSException {
      DbCAxiomContract found = finder.findAxiomContract(toSearch);
      TestGenerationUtil.compareAxiomContract(toSearch, found);
      IDbCProofReferencable proofReferencable = finder.findProofReferencable(toSearch);
      assertSame(found, proofReferencable);      
   }

   /**
    * Searches all elements in the {@link IDSConnection}.
    * @param model The root element.
    * @param connection The {@link IDSConnection} to search in.
    * @throws DSException Occurred Exception
    */
   public static void findAllElements(DbcModel model, IDSConnection connection) throws DSException {
      TestCase.assertNotNull(model);
      TestCase.assertNotNull(connection);
      IDSFinder dsFinder = FinderUtil.getDSFinder(connection);
      findAllElements(model, dsFinder);
      IDbcFinder dbcFinder = FinderUtil.getDbcFinder(connection, model);
      findAllElements(connection, dbcFinder);
   }
   
   /**
    * Searches all elements with help of the given {@link IDSFinder}.
    * @param root The root element.
    * @param finder The {@link IDSFinder} to search with.
    * @throws DSException Occurred Exception
    */
   public static void findAllElements(EObject root, IDSFinder finder) throws DSException {
      TestCase.assertNotNull(root);
      TestCase.assertNotNull(finder);
      findElement(root, finder);
      TreeIterator<EObject> iterator = root.eAllContents();
      while (iterator.hasNext()) {
         findElement(iterator.next(), finder);
      }
   }

   /**
    * Searches the element with the given {@link IDSFinder}.
    * @param element The element to search.
    * @param finder The {@link IDSFinder} to use.
    * @throws DSException Occurred Exception
    */
   public static void findElement(EObject element, IDSFinder finder) throws DSException {
      TestCase.assertNotNull(element);
      TestCase.assertNotNull(finder);
      // Test main diagram elements
      if (element instanceof DbcModel) {
         // Not supported in finder directly
      }
      else if (element instanceof DbcProperty) {
         // Not supported in finder directly
      }
      else if (element instanceof DbcPackage) {
         IDSPackage foundElement = finder.findPackage((DbcPackage)element);
         TestGenerationUtil.comparePackage(foundElement, (DbcPackage)element, true);
      }
      else if (element instanceof DbcClass) {
         if (((DbcClass)element).isAnonymous()) {
            try {
               finder.findClass((DbcClass)element);
               TestCase.fail();
            }
            catch (DSException e) {
               TestCase.assertEquals("Anonymous classes like \"" + ((DbcClass)element).getName() + "\" are not supported.", e.getMessage());
            }
         }
         else {
            IDSClass foundElement = finder.findClass((DbcClass)element);
            TestGenerationUtil.compareClass(foundElement, (DbcClass)element, true);
            IDSProvable provable = finder.findProvable((DbcClass)element);
            assertSame(foundElement, provable);            
         }
      }
      else if (element instanceof DbcInterface) {
         IDSInterface foundElement = finder.findInterface((DbcInterface)element);
         TestGenerationUtil.compareInterface(foundElement, (DbcInterface)element, true);
         IDSProvable provable = finder.findProvable((DbcInterface)element);
         assertSame(foundElement, provable);            
      }
      else if (element instanceof DbcEnum) {
         IDSEnum foundElement = finder.findEnum((DbcEnum)element);
         TestGenerationUtil.compareEnum(foundElement, (DbcEnum)element, true);
         IDSProvable provable = finder.findProvable((DbcEnum)element);
         assertSame(foundElement, provable);            
      }
      else if (element instanceof DbcEnumLiteral) {
         IDSEnumLiteral foundElement = finder.findEnumLiteral((DbcEnumLiteral)element);
         TestGenerationUtil.compareEnumLiteral(foundElement, (DbcEnumLiteral)element, true);
      }
      else if (element instanceof DbcAttribute) {
         IDSAttribute foundElement = finder.findAttribute((DbcAttribute)element);
         TestGenerationUtil.compareAttribute(foundElement, (DbcAttribute)element, true);
      }
      else if (element instanceof DbcAxiom) {
         IDSAxiom foundElement = finder.findAxiom((DbcAxiom)element);
         TestGenerationUtil.compareAxiom(foundElement, (DbcAxiom)element, true);
      }
      else if (element instanceof DbCAxiomContract) {
         IDSAxiomContract foundElement = finder.findAxiomContract((DbCAxiomContract)element);
         TestGenerationUtil.compareAxiomContract(foundElement, (DbCAxiomContract)element);
         IDSProvable provable = finder.findProvable((DbCAxiomContract)element);
         assertSame(foundElement, provable);            
      }
      else if (element instanceof DbcMethod) {
         IDSMethod foundElement = finder.findMethod((DbcMethod)element);
         TestGenerationUtil.compareMethod(foundElement, (DbcMethod)element, true);
         IDSProvable provable = finder.findProvable((DbcMethod)element);
         assertSame(foundElement, provable);            
      }
      else if (element instanceof DbcConstructor) {
         IDSConstructor foundElement = finder.findConstructor((DbcConstructor)element);
         TestGenerationUtil.compareConstructor(foundElement, (DbcConstructor)element, true);
         IDSProvable provable = finder.findProvable((DbcConstructor)element);
         assertSame(foundElement, provable);            
      }
      else if (element instanceof DbcInvariant) {
         IDSInvariant foundElement = finder.findInvariant((DbcInvariant)element);
         TestGenerationUtil.compareInvariant(foundElement, (DbcInvariant)element);
      }
      else if (element instanceof DbcOperationContract) {
         IDSOperationContract foundElement = finder.findOperationContract((DbcOperationContract)element);
         TestGenerationUtil.compareOperationContract(foundElement, (DbcOperationContract)element);
         IDSProvable provable = finder.findProvable((DbcOperationContract)element);
         assertSame(foundElement, provable);            
      }
      else if (element instanceof DbcProofObligation) {
         // Not supported in finder directly
      }
      else {
         TestCase.fail("Not allowed element: " + element);
      }
      // Test provable separate from diagram elements
      if (element instanceof IDbCProvable) {
         if (element instanceof DbcClass && ((DbcClass)element).isAnonymous()) {
            // Special handling for anonymous classes with expected exception
            try {
               finder.findProvable((IDbCProvable)element);
               TestCase.fail();
            }
            catch (DSException e) {
               TestCase.assertEquals("Anonymous classes like \"" + ((DbcClass)element).getName() + "\" are not supported.", e.getMessage());
            }
         }
         else {
            // Normal search with expected result
            IDSProvable foundElement = finder.findProvable((IDbCProvable)element);
            if (foundElement instanceof IDSOperationContract) {
               TestCase.assertTrue(element instanceof DbcOperationContract);
               TestGenerationUtil.compareOperationContract((IDSOperationContract)foundElement, (DbcOperationContract)element);
            }
            else if (foundElement instanceof IDSAxiomContract) {
               TestCase.assertTrue(element instanceof DbCAxiomContract);
               TestGenerationUtil.compareAxiomContract((IDSAxiomContract)foundElement, (DbCAxiomContract)element);
            }
            else if (foundElement instanceof IDSClass) {
               TestCase.assertTrue(element instanceof DbcClass);
               TestGenerationUtil.compareClass((IDSClass)foundElement, (DbcClass)element, true);
            }
            else if (foundElement instanceof IDSInterface) {
               TestCase.assertTrue(element instanceof DbcInterface);
               TestGenerationUtil.compareInterface((IDSInterface)foundElement, (DbcInterface)element, true);
            }
            else if (foundElement instanceof IDSEnum) {
               TestCase.assertTrue(element instanceof DbcEnum);
               TestGenerationUtil.compareEnum((IDSEnum)foundElement, (DbcEnum)element, true);
            }
            else if (foundElement instanceof IDSMethod) {
               TestCase.assertTrue(element instanceof DbcMethod);
               TestGenerationUtil.compareMethod((IDSMethod)foundElement, (DbcMethod)element, true);
            }
            else if (foundElement instanceof IDSConstructor) {
               TestCase.assertTrue(element instanceof DbcConstructor);
               TestGenerationUtil.compareConstructor((IDSConstructor)foundElement, (DbcConstructor)element, true);
            }
            else {
               TestCase.fail("Not allowed provable: " + foundElement);
            }
         }
      }
   }
   
   /**
    * Returns the {@link EObject} that is represented by the {@link SWTBotGefEditPart}.
    * @param editPart The given {@link SWTBotGefEditPart}.
    * @return The represented {@link EObject}.
    */
   public static EObject getEditModel(SWTBotGefEditPart editPart) {
      return (EObject)editPart.part().getAdapter(EObject.class);
   }
   
   /**
    * Returns all {@link SWTBotGefEditPart} that represents an {@link EObject} of the given class.
    * @param parent The parent to search on.
    * @param expectedClass The expected {@link EObject} class.
    * @return The found {@link SWTBotGefEditPart}s.
    */
   public static List<SWTBotGefEditPart> getEditPartsByModelClass(SWTBotGefEditor parent, Class<?> expectedClass) {
      return getEditPartsByModelClass(parent.rootEditPart(), expectedClass);
   }
   
   /**
    * Returns all {@link SWTBotGefEditPart} that represents an {@link EObject} of the given class.
    * @param parent The parent to search on.
    * @param expectedClass The expected {@link EObject} class.
    * @return The found {@link SWTBotGefEditPart}s.
    */
   public static List<SWTBotGefEditPart> getEditPartsByModelClass(SWTBotGefEditPart parent, Class<?> expectedClass) {
      List<SWTBotGefEditPart> result = new LinkedList<SWTBotGefEditPart>();
      EObject object = getEditModel(parent);
      if (object != null && expectedClass.isInstance(object)) {
         result.add(parent);
      }
      for (SWTBotGefEditPart child : parent.children()) {
         result.addAll(getEditPartsByModelClass(child, expectedClass));
      }
      return result;
   }
   
   /**
    * Opens a proof.
    * @param startProofListener The {@link LogStartProofJobListener} to use.
    * @param tree The tree that provides the context menu to open a proof.
    * @param pathToProofElement The element to select in the tree.
    */
   public static void openProof(LogStartProofJobListener startProofListener, SWTBotTree tree, String[] pathToProofElement) {
      TestUtilsUtil.selectInTree(tree, pathToProofElement);
      openProof(startProofListener, tree, 1);
   }

   /**
    * Opens a proof.
    * @param startProofListener The {@link LogStartProofJobListener} to use.
    * @param tree The tree that provides the context menu to open a proof.
    * @param waitCount The number of started proofs to wait for.
    */
   public static void openProof(LogStartProofJobListener startProofListener, SWTBotTree tree, int waitCount) {
      int oldCount = startProofListener.getFinishCount();
      tree.contextMenu("Open Proof").click();
      waitForProofOpening(startProofListener, oldCount, waitCount);
   }
   
   /**
    * Opens the proof.
    * @param startProofListener The {@link LogStartProofJobListener} to use.
    * @param editor The editor to open the proof in.
    * @param proofEditPart The element to select in the editor for that a proof should be opened. 
    */
   public static void openProof(LogStartProofJobListener startProofListener, SWTBotGefEditor editor, SWTBotGefEditPart proofEditPart) {
      editor.select(proofEditPart);
      openProof(startProofListener, editor, 1);
   }
   
   /**
    * Opens the proof.
    * @param startProofListener The {@link LogStartProofJobListener} to use.
    * @param editor The editor to open the proof in.
    * @param waitCount The number of started proofs to wait for.
    */
   public static void openProof(LogStartProofJobListener startProofListener, SWTBotGefEditor editor, int waitCount) {
      int oldCount = startProofListener.getFinishCount();
      editor.clickContextMenu("Open Proof");
      waitForProofOpening(startProofListener, oldCount, waitCount);
   }
   
   /**
    * Waits until at least one more proof is opened.
    * @param startProofListener The {@link LogStartProofJobListener} to use.
    * @param oldCount The old number of opened proofs.
    * @param waitCount The number of started proofs to wait for.
    */
   public static void waitForProofOpening(LogStartProofJobListener startProofListener, int oldCount, int waitCount) {
      while (startProofListener.getFinishCount() < oldCount + waitCount) {
         TestUtilsUtil.sleep(100);
      }
   }
   
   /**
    * Counts the number of loaded proofs via {@link StartProofJob}.
    * @author Martin Hentschel
    */
   public static class LogStartProofJobListener implements IStartProofJobListener {
      /**
       * The number of events.
       */
      private int finishCount = 0;
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void jobFinished(StartProofJobEvent e) {
         synchronized (this) {
            finishCount++;
         }
      }

      /**
       * Returns the number of events.
       * @return The number of events.
       */
      public int getFinishCount() {
         synchronized (this) {
            return finishCount;
         }
      }
   }
}