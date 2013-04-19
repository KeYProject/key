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

import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * Provides a basic implementation for something that contains packages,
 * classes, interfaces and enumerations like
 * {@link IDSPackage}s or {@link IDSConnection}s.
 * @author Martin Hentschel
 */
public interface IDSContainer {
   /**
    * Returns the sub packages.
    * @return The sub packages.
    * @throws DSException Occurred Exception
    */
   public List<IDSPackage> getPackages() throws DSException;

   /**
    * Returns the package with the given name or {@code null} if 
    * no package with that name exist.
    * @param name The package name.
    * @return The package or {@code null} if it doesn't exist.
    * @throws DSException Occurred Exception
    */
   public IDSPackage getPackage(String name) throws DSException;
   
   /**
    * Returns all contained classes.
    * @return The classes.
    * @throws DSException Occurred Exception
    */
   public List<IDSClass> getClasses() throws DSException;

   /**
    * Returns the class with the given name.
    * @param name The name.
    * @return The found {@link IDSClass} or {@code null} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public IDSClass getClass(String name) throws DSException;

   /**
    * Returns all contained interfaces.
    * @return The interfaces.
    * @throws DSException Occurred Exception
    */
   public List<IDSInterface> getInterfaces() throws DSException;

   /**
    * Returns the interface with the given name.
    * @param name The name.
    * @return The found {@link IDSInterface} or {@code null} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public IDSInterface getInterface(String name) throws DSException;

   /**
    * Returns all contained enumerations.
    * @return The enumerations.
    * @throws DSException Occurred Exception
    */
   public List<IDSEnum> getEnums() throws DSException;

   /**
    * Returns the enumeration with the given name.
    * @param name The name.
    * @return The found {@link IDSEnum} or {@code null} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public IDSEnum getEnum(String name) throws DSException;
}