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

package de.hentschel.visualdbc.datasource.model;

import java.util.List;
import java.util.Map;
import java.util.Properties;

import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * The driver and factory that creates the data source connections and provides
 * some meta data.
 * @author Martin Hentschel
 */
public interface IDSDriver {
   /**
    * Returns the required settings.
    * @return The required connection settings.
    */
   public List<IDSConnectionSetting> getConnectionSettings();
   
   /**
    * Returns the priority with that the data sources are sorted.
    * @return The priority
    */
   public int getPriority();
   
   /**
    * Returns the unique ID of the driver. 
    * @return The unique ID.
    */
   public String getId();
   
   /**
    * Returns the data source name.
    * @return The data source name.
    */
   public String getName();
   
   /**
    * Creates a new unconnected {@link IDSConnection}.
    * @return The created {@link IDSConnection}.
    * @throws DSException Occurred Exception
    */
   public IDSConnection createConnection() throws DSException;
   
   /**
    * Converts the connection settings that are used in
    * {@link IDSConnection#connect(Map, boolean, org.eclipse.core.runtime.IProgressMonitor)} to
    * define the connection parameters into simple {@link String} values that can be used for persistent.
    * @param connectionSettings The original connection settings.
    * @return The converted connection settings with {@link String} values for persistent.
    */
   public Properties toPersistentProperties(Map<String, Object> connectionSettings);
   
   /**
    * Loads the connection properties from the persistent once.
    * @param persistentProperties The persistent properties.
    * @return The connection settings usable in {@link IDSConnection#connect(Map, boolean, org.eclipse.core.runtime.IProgressMonitor)}
    */
   public Map<String, Object> fromPersistentProperties(Properties persistentProperties);
}