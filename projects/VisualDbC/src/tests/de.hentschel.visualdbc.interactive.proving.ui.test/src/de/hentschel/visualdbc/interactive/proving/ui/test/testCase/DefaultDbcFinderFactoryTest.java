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

package de.hentschel.visualdbc.interactive.proving.ui.test.testCase;

import junit.framework.TestCase;

import org.eclipse.core.runtime.AssertionFailedException;
import org.junit.Test;

import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;
import de.hentschel.visualdbc.generation.test.util.TestGenerationUtil;
import de.hentschel.visualdbc.interactive.proving.ui.finder.DefaultDbcFinder;
import de.hentschel.visualdbc.interactive.proving.ui.finder.DefaultDbcFinderFactory;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDbcFinder;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDbcFinderFactory;

/**
 * Tests for {@link DefaultDbcFinderFactory}
 * @author Martin Hentschel
 */
public class DefaultDbcFinderFactoryTest extends TestCase {
   /**
    * Tests {@link DefaultDbcFinderFactory#createFinder(de.hentschel.visualdbc.dbcmodel.DbcModel)}
    */
   @Test
   public void testCreateFinder() {
      IDSConnection connection = null;
      try {
         IDbcFinderFactory factory = new DefaultDbcFinderFactory();
         connection = TestGenerationUtil.createDummyConnection();
         IDbcFinder finder = factory.createFinder(DbcmodelFactory.eINSTANCE.createDbcModel());
         assertNotNull(finder);
         assertTrue(finder instanceof DefaultDbcFinder);
         try {
            factory.createFinder(null);
            fail();
         }
         catch (AssertionFailedException e) {
         }
      }
      finally {
         TestGenerationUtil.closeConnection(connection);
      }
   }
   
   /**
    * Tests {@link DefaultDbcFinderFactory#canHandle(de.hentschel.visualdbc.datasource.model.IDSConnection)}
    */
   @Test
   public void testCanHandle() {
      IDSConnection connection = null;
      try {
         IDbcFinderFactory factory = new DefaultDbcFinderFactory();
         assertFalse(factory.canHandle(null));
         connection = TestGenerationUtil.createDummyConnection();
         assertTrue(factory.canHandle(connection));
      }
      finally {
         TestGenerationUtil.closeConnection(connection);
      }
   }
   
   /**
    * Tests {@link DefaultDbcFinderFactory#getPriority()}
    */
   @Test
   public void testGetPriority() {
      IDbcFinderFactory factory = new DefaultDbcFinderFactory();
      assertEquals(Integer.MIN_VALUE, factory.getPriority());
   }
}