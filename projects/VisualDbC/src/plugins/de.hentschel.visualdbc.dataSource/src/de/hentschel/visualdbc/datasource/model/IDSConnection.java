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

package de.hentschel.visualdbc.datasource.model;

import java.util.Map;

import org.eclipse.core.runtime.IProgressMonitor;

import de.hentschel.visualdbc.datasource.model.event.IDSConnectionListener;
import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * Represents the connection to a data source.
 * @author Martin Hentschel
 */
public interface IDSConnection extends IDSContainer {
   /**
    * Returns the {@link IDSDriver} that has created this connection.
    * @return The {@link IDSDriver}.
    */
   public IDSDriver getDriver();
   
   /**
    * Opens the connection to the data source.
    * @param connectionSettings The connection settings.
    * @param interactive {@code false} = no user interactions, {@code true} = user interactions required
    * @param monitor The {@link IProgressMonitor} to visualize the connection progress.
    * @throws DSException Occurred Exception
    */
   public void connect(Map<String, Object> connectionSettings,
                       boolean interactive,
                       IProgressMonitor monitor) throws DSException;
   
   /**
    * Checks if the current connection is interactive or not.
    * @return {@code false} = no user interactions, {@code true} = user interactions required
    * @throws DSException Occurred Exception
    */
   public boolean isInteractive() throws DSException;
   
   /**
    * Checks if the connection is established.
    * @return {@code true} = connected, {@code false} = disconnected
    * @throws DSException Occurred Exception
    */
   public boolean isConnected() throws DSException;
   
   /**
    * Closes the connection to the data source
    * @throws DSException Occurred Exception
    */
   public void disconnect() throws DSException;
   
   /**
    * Returns the used connection settings defined in
    * {@link #connect(Map, boolean, IProgressMonitor)}.
    * @return The used connection settings.
    */
   public Map<String, Object> getConnectionSettings();
   
   /**
    * Adds the new listener.
    * @param l The listener to add.
    */
   public void addConnectionListener(IDSConnectionListener l);

   /**
    * Removes the listener.
    * @param l The listener to remove.
    */
   public void removeConnectionListener(IDSConnectionListener l);
   
   /**
    * Returns all listeners.
    * @return The available listeners.
    */
   public IDSConnectionListener[] getConnectionListeners();
}