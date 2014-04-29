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
public interface IDSInterface extends IDSType {   
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
    * Returns all extend references that have a target that is contained in the model.
    * @return The extend references.
    * @throws DSException Occurred Exception
    */
   public List<IDSInterface> getExtends() throws DSException;
   
   /**
    * Returns the names of all super classes also if they are not included
    * in the model.
    * @return The name of all super interfaces.
    * @throws DSException Occurred Exception
    */
   public List<String> getExtendsFullnames() throws DSException;
}