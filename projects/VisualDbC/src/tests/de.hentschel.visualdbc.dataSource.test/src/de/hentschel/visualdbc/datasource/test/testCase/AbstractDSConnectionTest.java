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

package de.hentschel.visualdbc.datasource.test.testCase;

import java.util.HashMap;

import junit.framework.TestCase;

import org.junit.Test;

import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.implementation.AbstractDSConnection;
import de.hentschel.visualdbc.datasource.model.memory.MemoryConnection;
import de.hentschel.visualdbc.datasource.test.util.ConnectionLogger;
import de.hentschel.visualdbc.datasource.test.util.TestDataSourceUtil;

/**
 * Contains tests for {@link AbstractDSConnection}
 * @author Martin Hentschel
 */
public class AbstractDSConnectionTest extends TestCase {
   /**
    * Tests for 
    * {@link AbstractDSConnection#addConnectionListener(de.hentschel.visualdbc.generation.model.event.IDSConnectionListener)}
    * {@link AbstractDSConnection#getConnectionListeners()}
    * {@link AbstractDSConnection#removeConnectionListener(de.hentschel.visualdbc.generation.model.event.IDSConnectionListener)} and
    * and throwing events.
    */
   @Test
   public void testListenerManagement() {
      try {
         // Create logger
         ConnectionLogger logger = new ConnectionLogger();
         // Create connection
         MemoryConnection connection = new MemoryConnection();
         assertEquals(0, connection.getConnectionListeners().length);
         connection.addConnectionListener(logger);
         assertEquals(1, connection.getConnectionListeners().length);
         // Connect
         TestDataSourceUtil.compareConnectionEvents(connection, logger, false, false, false);
         connection.connect(new HashMap<String, Object>(), false, null);
         TestDataSourceUtil.compareConnectionEvents(connection, logger, true, true, false);
         // Disconnect
         TestDataSourceUtil.compareConnectionEvents(connection, logger, true, false, false);
         connection.disconnect();
         TestDataSourceUtil.compareConnectionEvents(connection, logger, false, false, true);
         // Remove listener
         TestDataSourceUtil.compareConnectionEvents(connection, logger, false, false, false);
         assertEquals(1, connection.getConnectionListeners().length);
         connection.removeConnectionListener(logger);
         assertEquals(0, connection.getConnectionListeners().length);
      }
      catch (DSException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
   }
}