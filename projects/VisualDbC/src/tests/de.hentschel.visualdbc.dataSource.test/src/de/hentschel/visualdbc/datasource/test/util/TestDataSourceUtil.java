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

package de.hentschel.visualdbc.datasource.test.util;

import junit.framework.TestCase;
import de.hentschel.visualdbc.datasource.model.DSPackageManagement;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSDriver;
import de.hentschel.visualdbc.datasource.model.event.DSConnectionEvent;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.test.dummyModel.DummyModelDriver;
import de.hentschel.visualdbc.datasource.util.DriverUtil;

/**
 * Provides static methods that make testing easier.
 * @author Martin Hentschel
 */
public final class TestDataSourceUtil {
   /**
    * Forbid instances.
    */
   private TestDataSourceUtil() {
   }
   
   /**
    * Returns the dummy {@link IDSDriver}.
    * @return The dummy {@link IDSDriver}.
    */
   public static IDSDriver getDummyDriver() {
      return DriverUtil.getDriver(DummyModelDriver.ID);
   }

   /**
    * Compares the caught events with the expected ones.
    * @param con The {@link IDSConnection} to use.
    * @param logger the {@link ConnectionLogger} to use.
    * @param connected Should {@link IDSConnection} be connected?
    * @param connectionEvent Should exists one connected event?
    * @param disconnectEvent Should exists one disconnected event?
    * @throws DSException Occurred Exception
    */
   public static void compareConnectionEvents(IDSConnection con, 
                                              ConnectionLogger logger, 
                                              boolean connected, 
                                              boolean connectionEvent, 
                                              boolean disconnectEvent) throws DSException {
      TestCase.assertNotNull(con);
      TestCase.assertEquals(connected, con.isConnected());
      TestCase.assertEquals(connectionEvent ? 1 : 0, logger.getConnected().size());
      if (connectionEvent) {
         DSConnectionEvent event = logger.getConnected().get(0);
         TestCase.assertEquals(con, event.getSource());
      }
      TestCase.assertEquals(disconnectEvent ? 1 : 0, logger.getDisconnected().size());
      if (disconnectEvent) {
         DSConnectionEvent event = logger.getDisconnected().get(0);
         TestCase.assertEquals(con, event.getSource());
      }
      logger.getConnected().clear();
      logger.getDisconnected().clear();
   }
   
   /**
    * Returns the index of {@link DSPackageManagement} in
    * {@link DSPackageManagement#values()}.
    * @param packageManagement The {@link DSPackageManagement} to search.
    * @return The index or {@code -1} if it was not found.
    */
   public static int indexOf(DSPackageManagement packageManagement) {
      int index = -1;
      int i = 0;
      while (i < DSPackageManagement.values().length && index < 0) {
         if (DSPackageManagement.values()[i].equals(packageManagement)) {
            index = i;
         }
         i++;
      }
      return index;
   }
}