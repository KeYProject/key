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
import de.hentschel.visualdbc.generation.test.util.TestGenerationUtil;
import de.hentschel.visualdbc.interactive.proving.ui.finder.DefaultDSFinder;
import de.hentschel.visualdbc.interactive.proving.ui.finder.DefaultDSFinderFactory;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDSFinder;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDSFinderFactory;

/**
 * Tests for {@link DefaultDSFinderFactory}
 * @author Martin Hentschel
 */
public class DefaultDSFinderFactoryTest extends TestCase {
   /**
    * Tests {@link DefaultDSFinderFactory#createFinder(IDSConnection)}
    */
   @Test
   public void testCreateFinder() {
      IDSConnection connection = null;
      try {
         IDSFinderFactory factory = new DefaultDSFinderFactory();
         connection = TestGenerationUtil.createDummyConnection();
         IDSFinder finder = factory.createFinder(connection);
         assertNotNull(finder);
         assertTrue(finder instanceof DefaultDSFinder);
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
    * Tests {@link DefaultDSFinderFactory#canHandle(de.hentschel.visualdbc.datasource.model.IDSConnection)}
    */
   @Test
   public void testCanHandle() {
      IDSConnection connection = null;
      try {
         IDSFinderFactory factory = new DefaultDSFinderFactory();
         assertFalse(factory.canHandle(null));
         connection = TestGenerationUtil.createDummyConnection();
         assertTrue(factory.canHandle(connection));
      }
      finally {
         TestGenerationUtil.closeConnection(connection);
      }
   }
   
   /**
    * Tests {@link DefaultDSFinderFactory#getPriority()}
    */
   @Test
   public void testGetPriority() {
      IDSFinderFactory factory = new DefaultDSFinderFactory();
      assertEquals(Integer.MIN_VALUE, factory.getPriority());
   }
}