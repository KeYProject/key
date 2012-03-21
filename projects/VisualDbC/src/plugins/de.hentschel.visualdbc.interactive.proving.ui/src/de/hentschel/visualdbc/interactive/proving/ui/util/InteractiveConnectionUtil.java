/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package de.hentschel.visualdbc.interactive.proving.ui.util;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.runtime.IProgressMonitor;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSDriver;
import de.hentschel.visualdbc.datasource.model.event.DSConnectionAdapter;
import de.hentschel.visualdbc.datasource.model.event.DSConnectionEvent;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.util.DriverUtil;
import de.hentschel.visualdbc.dbcmodel.DbcModel;

/**
 * <p>
 * Provides some static methods to work with interactive data source connections.
 * </p>
 * <p>
 * For each domain model resource exists only one shared interactive data source connection.
 * This one is opened via {@link #openConnection(DbcModel, IProgressMonitor)} if needed.
 * If one connection is already opened, this one is returned. The interactive connection is automatically
 * removed from the internal {@link Map} when it is disconnected. In this case the next call of
 * {@link #openConnection(DbcModel, IProgressMonitor)} opens a new connection.
 * </p>
 * @author Martin Hentschel
 */
public final class InteractiveConnectionUtil {
   /**
    * The currently opened interactive {@link IDSConnection}.
    */
   private static Map<DbcModel, IDSConnection> connections = new HashMap<DbcModel, IDSConnection>();
   
   /**
    * Forbid instances.
    */
   private InteractiveConnectionUtil() {
   }
   
   /**
    * Opens the {@link IDSConnection} for the {@link DbcModel}. If a connection
    * already exists with the same connection settings and is still established
    * this one is returned instead of opening a new connection.
    * @param model The {@link DbcModel} to open connection for.
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The opened {@link IDSConnection}.
    * @throws DSException Occurred Exception.
    */
   public static IDSConnection openConnection(DbcModel model,
                                              IProgressMonitor monitor) throws DSException {
      // Check model
      if (model == null) {
         throw new DSException("Diagram root is null.");
      }
      // Make sure that the model has a driver id
      if (StringUtil.isTrimmedEmpty(model.getDriverId())) {
         throw new DSException("No driver ID defined in model root.");
      }
      // Get driver
      IDSDriver driver = DriverUtil.getDriver(model.getDriverId());
      if (driver == null) {
         throw new DSException("Can't find driver for ID \"" + model.getDriverId() + "\".");
      }
      // Get connection settings
      Map<String, Object> connectionSettings = driver.fromPersistentProperties(model.toConnectionProperties()); 
      // Check if a connection already exists
      IDSConnection result = connections.get(model);
      if (result == null) {
         result = driver.createConnection();
         result.addConnectionListener(new ConnectionCloseListener(model));
         connections.put(model, result);
      }
      // Make sure that the connection is established
      if (!result.isConnected()) {
         result.connect(connectionSettings, true, monitor);
      }
      // Check that the correct connection is established
      if (result.getDriver() == null) {
         throw new DSException("Current data source connection has no driver reference.");
      }
      if (!result.isInteractive()) {
         throw new DSException("Connection is not interactive.");
      }
      if (!ObjectUtil.equals(model.getDriverId(), result.getDriver().getId())) {
         throw new DSException("Connected to wrong data source. Current driver has ID \"" + result.getDriver().getId() + "\" but expcted \"" + model.getDriverId() + "\".");
      }
      if (!ObjectUtil.equals(connectionSettings, result.getConnectionSettings())) {
         throw new DSException("Connection settings in diagram root and current connection are different.");
      }
      return result;
   }
   
   /**
    * Checks if a {@link IDSConnection} is opened for the given {@link DbcModel}.
    * @param model The {@link DbcModel} to check.
    * @return {@code true} connection is opened, {@code false} = connection is not opened.
    * @throws DSException Occurred Exception.
    */
   public static boolean isOpened(DbcModel model) throws DSException {
      if (model != null) {
         IDSConnection connection = connections.get(model);
         return connection != null && connection.isConnected();
      }
      else {
         return false;
      }
   }
   
   /**
    * Closes the {@link IDSConnection} for the {@link DbcModel}.
    * @param model The {@link DbcModel} to close connection for.
    * @throws DSException Occurred Exception.
    */
   public static void closeConnection(DbcModel model) throws DSException {
      if (model != null) {
         IDSConnection connection = connections.remove(model);
         if (connection != null && connection.isConnected()) {
            connection.disconnect();
         }
      }
   }

   /**
    * Listens for connection close events and removes the connection
    * from the static {@link Map} {@link InteractiveConnectionUtil#connections}.
    * @author Martin Hentschel
    */
   private static class ConnectionCloseListener extends DSConnectionAdapter {
      /**
       * The {@link DbcModel} that is used as key in {@link InteractiveConnectionUtil#connections}.
       */
      private DbcModel model;
      
      /**
       * Constructor.
       * @param model The {@link DbcModel} that is used as key in {@link InteractiveConnectionUtil#connections}.
       */
      private ConnectionCloseListener(DbcModel model) {
         super();
         this.model = model;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void disconnected(DSConnectionEvent e) {
         try {
            e.getSource().removeConnectionListener(this);
            closeConnection(model);
         }
         catch (DSException exception) {
            LogUtil.getLogger().logError(exception);
         }
      }
   }
}
