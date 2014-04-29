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

package de.hentschel.visualdbc.interactive.proving.ui.test.testCase;

import java.util.Iterator;
import java.util.List;

import junit.framework.TestCase;

import org.junit.Test;

import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;
import de.hentschel.visualdbc.generation.test.util.TestGenerationUtil;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDSFinder;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDSFinderFactory;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDbcFinder;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDbcFinderFactory;
import de.hentschel.visualdbc.interactive.proving.ui.test.dummyFinder.DSFinderFactory0;
import de.hentschel.visualdbc.interactive.proving.ui.test.dummyFinder.DSFinderFactory1;
import de.hentschel.visualdbc.interactive.proving.ui.test.dummyFinder.DSFinderFactory2;
import de.hentschel.visualdbc.interactive.proving.ui.test.dummyFinder.DSFinderFactoryMinus1;
import de.hentschel.visualdbc.interactive.proving.ui.test.dummyFinder.DSFinderFactoryMinus2;
import de.hentschel.visualdbc.interactive.proving.ui.test.dummyFinder.DbcFinderFactory0;
import de.hentschel.visualdbc.interactive.proving.ui.test.dummyFinder.DbcFinderFactory1;
import de.hentschel.visualdbc.interactive.proving.ui.test.dummyFinder.DbcFinderFactory2;
import de.hentschel.visualdbc.interactive.proving.ui.test.dummyFinder.DbcFinderFactoryMinus1;
import de.hentschel.visualdbc.interactive.proving.ui.test.dummyFinder.DbcFinderFactoryMinus2;
import de.hentschel.visualdbc.interactive.proving.ui.test.dummyFinder.DSFinderFactory1.Finder1;
import de.hentschel.visualdbc.interactive.proving.ui.util.FinderUtil;

/**
 * Tests for {@link FinderUtil}.
 * @author Martin Hentschel
 */
public final class FinderUtilTest extends TestCase {
   /**
    * Tests {@link FinderUtil#getDbcFinder(IDSConnection, de.hentschel.visualdbc.dbcmodel.DbcModel)}
    */
   @Test
   public void testGetDbcFinder() {
      // Create dummy connection
      IDSConnection dummyConnection = TestGenerationUtil.createDummyConnection();
      // Get finder
      DbcModel model = DbcmodelFactory.eINSTANCE.createDbcModel();
      IDbcFinder finder = FinderUtil.getDbcFinder(dummyConnection, model);
      assertEquals(de.hentschel.visualdbc.interactive.proving.ui.test.dummyFinder.DbcFinderFactory1.Finder1.class, finder.getClass());
      assertSame(model, finder.getModel());
      // Get finder again
      IDbcFinder finderAgain = FinderUtil.getDbcFinder(dummyConnection, model);
      assertEquals(de.hentschel.visualdbc.interactive.proving.ui.test.dummyFinder.DbcFinderFactory1.Finder1.class, finderAgain.getClass());
      assertSame(model, finder.getModel());
   }
   
   /**
    * Tests {@link FinderUtil#getDbcFinderFactory(IDSConnection)}
    */
   @Test
   public void testGetDbcFinderFactory() {
      // Create dummy connection
      IDSConnection dummyConnection = TestGenerationUtil.createDummyConnection();
      // Get finder factory
      IDbcFinderFactory factory = FinderUtil.getDbcFinderFactory(dummyConnection);
      assertEquals(DbcFinderFactory1.class, factory.getClass());
      // Get finder factory again
      IDbcFinderFactory factoryAgain = FinderUtil.getDbcFinderFactory(dummyConnection);
      assertSame(factory, factoryAgain);
   }
   
   /**
    * Tests {@link FinderUtil#getDbcFinderFactories()}
    */
   @Test
   public void testGetDbcFinderFactories() {
      // Get factories
      List<IDbcFinderFactory> factories = FinderUtil.getDbcFinderFactories();
      // Test size
      assertTrue(factories.size() >= 5);
      // Test order of factories
      int factoryMinus2 = indexOfFactory(factories, DbcFinderFactoryMinus2.class);
      int factoryMinus1 = indexOfFactory(factories, DbcFinderFactoryMinus1.class);
      int factory0 = indexOfFactory(factories, DbcFinderFactory0.class);
      int factory1 = indexOfFactory(factories, DbcFinderFactory1.class);
      int factory2 = indexOfFactory(factories, DbcFinderFactory2.class);
      assertTrue(factoryMinus2 >= 0);
      assertTrue(factoryMinus1 > factoryMinus2);
      assertTrue(factory0 > factoryMinus1);
      assertTrue(factory1 >= factory0);
      assertTrue(factory2 >= factory1);
      // Get factories again to make sure that they return the same instances
      List<IDbcFinderFactory> factoriesAgain = FinderUtil.getDbcFinderFactories();
      assertEquals(factories.size(), factoriesAgain.size());
      Iterator<IDbcFinderFactory> firstIter = factories.iterator();
      Iterator<IDbcFinderFactory> againIter = factoriesAgain.iterator();
      while (firstIter.hasNext() && againIter.hasNext()) {
         assertSame(firstIter.next(), againIter.next());
      }
      assertFalse(firstIter.hasNext());
      assertFalse(againIter.hasNext());
   }
   
   /**
    * Tests {@link FinderUtil#getDSFinder(IDSConnection)}
    */
   @Test
   public void testGetDSFinder() {
      // Create dummy connection
      IDSConnection dummyConnection = TestGenerationUtil.createDummyConnection();
      // Get finder
      IDSFinder finder = FinderUtil.getDSFinder(dummyConnection);
      assertEquals(Finder1.class, finder.getClass());
      // Get finder again
      IDSFinder finderAgain = FinderUtil.getDSFinder(dummyConnection);
      assertEquals(Finder1.class, finderAgain.getClass());
   }
   
   /**
    * Tests {@link FinderUtil#getDSFinderFactory(de.hentschel.visualdbc.datasource.model.IDSConnection)}
    */
   @Test
   public void testGetDSFinderFactory() {
      // Create dummy connection
      IDSConnection dummyConnection = TestGenerationUtil.createDummyConnection();
      // Get finder factory
      IDSFinderFactory factory = FinderUtil.getDSFinderFactory(dummyConnection);
      assertEquals(DSFinderFactory1.class, factory.getClass());
      // Get finder factory again
      IDSFinderFactory factoryAgain = FinderUtil.getDSFinderFactory(dummyConnection);
      assertSame(factory, factoryAgain);
   }
   
   /**
    * Tests {@link FinderUtil#getDSFinderFactories()}
    */
   @Test
   public void testGetDSFinderFactories() {
      // Get factories
      List<IDSFinderFactory> factories = FinderUtil.getDSFinderFactories();
      // Test size
      assertTrue(factories.size() >= 5);
      // Test order of factories
      int factoryMinus2 = indexOfFactory(factories, DSFinderFactoryMinus2.class);
      int factoryMinus1 = indexOfFactory(factories, DSFinderFactoryMinus1.class);
      int factory0 = indexOfFactory(factories, DSFinderFactory0.class);
      int factory1 = indexOfFactory(factories, DSFinderFactory1.class);
      int factory2 = indexOfFactory(factories, DSFinderFactory2.class);
      assertTrue(factoryMinus2 >= 0);
      assertTrue(factoryMinus1 > factoryMinus2);
      assertTrue(factory0 > factoryMinus1);
      assertTrue(factory1 >= factory0);
      assertTrue(factory2 >= factory1);
      // Get factories again to make sure that they return the same instances
      List<IDSFinderFactory> factoriesAgain = FinderUtil.getDSFinderFactories();
      assertEquals(factories.size(), factoriesAgain.size());
      Iterator<IDSFinderFactory> firstIter = factories.iterator();
      Iterator<IDSFinderFactory> againIter = factoriesAgain.iterator();
      while (firstIter.hasNext() && againIter.hasNext()) {
         assertSame(firstIter.next(), againIter.next());
      }
      assertFalse(firstIter.hasNext());
      assertFalse(againIter.hasNext());
   }

   /**
    * Returns the index of the factory with the given class in the {@link List}.
    * @param factories All factories.
    * @param classInstance All class instances.
    * @return The index or {@code -1} if it was not found.
    */
   protected static int indexOfFactory(List<?> factories, Class<?> classInstance) {
      int result = -1;
      Iterator<?> iter = factories.iterator();
      int i = 0;
      while (result < 0 && iter.hasNext()) {
         if (classInstance.equals(iter.next().getClass())) {
            result = i;
         }
         i++;
      }
      return result;
   }
}