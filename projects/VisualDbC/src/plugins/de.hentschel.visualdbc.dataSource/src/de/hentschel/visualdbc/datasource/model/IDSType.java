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
 * Represents an abstract type on the data source.
 * @author Martin Hentschel
 */
public interface IDSType extends IDSProvable {
   /**
    * Returns all contained attributes.
    * @return The contained attributes.
    * @throws DSException Occurred Exception
    */
   public List<IDSAttribute> getAttributes() throws DSException;

   /**
    * Returns the attribute with the given name.
    * @param definition The name.
    * @return The found {@link IDSAttribute} or {@code null} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public IDSAttribute getAttribute(String name) throws DSException;
   
   /**
    * Returns the parent {@link IDSPackage} or {@link IDSContainer} or
    * {@code null} if it has no one. 
    * @return The parent {@link IDSContainer} or {@code null} if it has no one.
    */
   public IDSContainer getParentContainer();
   
   /**
    * Returns the parent {@link IDSType} if it is an inner type or {@code null}
    * if it is not an inner type.
    * @return The parent {@link IDSType} or {@code null}.
    */
   public IDSType getParentType();
   
   /**
    * Returns the type name.
    * @return The type name.
    * @throws DSException Occurred Exception
    */
   public String getName() throws DSException;
   
   /**
    * Returns the visibility.
    * @return The visibility.
    * @throws DSException Occurred Exception
    */
   public DSVisibility getVisibility() throws DSException;
   
   /**
    * Checks if it is static.
    * @return Is static?
    * @throws DSException Occurred Exception
    */
   public boolean isStatic() throws DSException;

   /**
    * Returns all inner classes.
    * @return The classes.
    * @throws DSException Occurred Exception
    */
   public List<IDSClass> getInnerClasses() throws DSException;
   
   /**
    * Returns the class with the given name or {@code null} if 
    * no class with that name exist.
    * @param name The class name.
    * @return The class or {@code null} if it doesn't exist.
    * @throws DSException Occurred Exception
    */
   public IDSClass getInnerClass(String name) throws DSException;   

   /**
    * Returns all inner interfaces.
    * @return The interfaces.
    * @throws DSException Occurred Exception
    */
   public List<IDSInterface> getInnerInterfaces() throws DSException;

   /**
    * Returns the interface with the given name or {@code null} if 
    * no interface with that name exist.
    * @param name The interface name.
    * @return The interface or {@code null} if it doesn't exist.
    * @throws DSException Occurred Exception
    */
   public IDSInterface getInnerInterface(String name) throws DSException;   
   
   /**
    * Returns all inner enumerations.
    * @return The enumerations.
    * @throws DSException Occurred Exception
    */
   public List<IDSEnum> getInnerEnums() throws DSException;

   /**
    * Returns the enumeration with the given name or {@code null} if 
    * no enumeration with that name exist.
    * @param name The enumeration name.
    * @return The enumeration or {@code null} if it doesn't exist.
    * @throws DSException Occurred Exception
    */
   public IDSEnum getInnerEnum(String name) throws DSException;
   
   /**
    * Returns all contained invariants.
    * @return The contained invariants.
    * @throws DSException Occurred Exception
    */
   public List<IDSInvariant> getInvariants() throws DSException;

   /**
    * Returns the invariant with the given condition.
    * @param definition The condition.
    * @return The found {@link IDSInvariant} or {@code null} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public IDSInvariant getInvariant(String condition) throws DSException;

   /**
    * Returns the axiom with the given definition.
    * @param definition The definition.
    * @return The found {@link IDSAxiom} or {@code null} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public IDSAxiom getAxiom(String definition) throws DSException;
   
   /**
    * Returns all contained axioms.
    * @return The contained axioms.
    * @throws DSException Occurred Exception
    */
   public List<IDSAxiom> getAxioms() throws DSException;
}