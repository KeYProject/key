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

package de.hentschel.visualdbc.datasource.model.memory;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.IProgressMonitor;

import de.hentschel.visualdbc.datasource.model.IDSClass;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSDriver;
import de.hentschel.visualdbc.datasource.model.IDSEnum;
import de.hentschel.visualdbc.datasource.model.IDSInterface;
import de.hentschel.visualdbc.datasource.model.IDSPackage;
import de.hentschel.visualdbc.datasource.model.event.DSConnectionEvent;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.implementation.AbstractDSConnection;

/**
 * Default implementation for an {@link IDSConnection} for objects in the
 * memory.
 * @author Martin Hentschel
 */
public class MemoryConnection extends AbstractDSConnection {
   /**
    * The {@link IDSDriver} that has created this connection.
    */
   private IDSDriver driver;
   
   /**
    * Indicates if a connection is established or not.
    */
   private boolean connected = false;
   
   /**
    * {@code false} = no user interactions, {@code true} = user interactions required
    */
   private boolean interactive;

   /**
    * The contained packages.
    */
   private List<IDSPackage> packages = new LinkedList<IDSPackage>();

   /**
    * The contained classes.
    */
   private List<IDSClass> classes = new LinkedList<IDSClass>();

   /**
    * The contained interfaces.
    */
   private List<IDSInterface> interfaces = new LinkedList<IDSInterface>();

   /**
    * The contained enumerations.
    */
   private List<IDSEnum> enums = new LinkedList<IDSEnum>();
   
   /**
    * The used connection settings defined in
    * {@link #connect(Map, boolean, IProgressMonitor)}.
    */
   private Map<String, Object> connectionSettings;
   
   /**
    * Default constructor.
    */
   public MemoryConnection() {
   }
   
   /**
    * Constructor.
    * @param driver The {@link IDSDriver} that has created this connection.
    */
   public MemoryConnection(IDSDriver driver) {
      super();
      this.driver = driver;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void connect(Map<String, Object> connectionSettings, 
                       boolean interactive,
                       IProgressMonitor monitor) throws DSException {
      this.connectionSettings = connectionSettings;
      this.interactive = interactive;
      boolean wasConnected = this.connected;
      this.connected = true;
      if (wasConnected != this.connected) {
         fireConnected(new DSConnectionEvent(this));
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isConnected() {
      return connected;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void disconnect() throws DSException {
      boolean wasConnected = connected;
      connected = false;
      if (wasConnected != connected) {
         fireDisconnected(new DSConnectionEvent(this));
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSPackage> getPackages() {
      return packages;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSClass> getClasses() {
      return classes;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSInterface> getInterfaces() {
      return interfaces;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSEnum> getEnums() {
      return enums;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSDriver getDriver() {
      return driver;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Map<String, Object> getConnectionSettings() {
      return connectionSettings;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isInteractive() throws DSException {
      return interactive;
   }
   
   /**
    * Adds the child package and updates the parent reference on it.
    * @param child The new child package to add.
    */
   public void addPackage(MemoryPackage child) {
      getPackages().add(child);
      child.setParent(this);
   }
   
   /**
    * Adds the child class and updates the parent reference on it.
    * @param child The new child class to add.
    */
   public void addClass(MemoryClass child) {
      getClasses().add(child);
      child.setParentContainer(this);
   }
   
   /**
    * Adds the child interface and updates the parent reference on it.
    * @param child The new child interface to add.
    */
   public void addInterface(MemoryInterface child) {
      getInterfaces().add(child);
      child.setParentContainer(this);
   }
   
   /**
    * Adds the child enumeration and updates the parent reference on it.
    * @param child The new child enumeration to add.
    */
   public void addEnum(MemoryEnum child) {
      getEnums().add(child);
      child.setParentContainer(this);
   }
}