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

import java.util.List;

import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * Represents an interface on the data source.
 * @author Martin Hentschel
 */
public interface IDSEnum extends IDSType {   
   /**
    * Returns all contained methods.
    * @return The contained methods.
    * @throws DSException Occurred Exception
    */
   public List<IDSMethod> getMethods() throws DSException;
   
   /**
    * Returns the method with the given signature.
    * @param signature The signature.
    * @return The found {@link IDSMethod} or {@code null} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public IDSMethod getMethod(String signature) throws DSException;
   
   /**
    * Returns all contained constructors.
    * @return The contained constructors.
    * @throws DSException Occurred Exception
    */
   public List<IDSConstructor> getConstructors() throws DSException;

   /**
    * Returns the constructor with the given signature.
    * @param signature The signature.
    * @return The found {@link IDSConstructor} or {@code null} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public IDSConstructor getConstructor(String signature) throws DSException;
   
   /**
    * Returns all contained literals.
    * @return The contained literals.
    * @throws DSException Occurred Exception
    */
   public List<IDSEnumLiteral> getLiterals() throws DSException;
   
   /**
    * Returns the enumeration literal with the given name.
    * @param name The name.
    * @return The found {@link IDSEnumLiteral} or {@code null} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public IDSEnumLiteral getLiteral(String name) throws DSException;
   
   /**
    * Returns all implements references that have a target that is contained in the model.
    * @return The implements references.
    * @throws DSException Occurred Exception
    */
   public List<IDSInterface> getImplements() throws DSException;
   
   /**
    * Returns the names of all super interfaces also if they are not included
    * in the model.
    * @return The name of all super interfaces.
    * @throws DSException Occurred Exception
    */
   public List<String> getImplementsFullnames() throws DSException;
}