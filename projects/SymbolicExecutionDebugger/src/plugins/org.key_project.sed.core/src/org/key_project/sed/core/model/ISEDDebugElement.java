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

package org.key_project.sed.core.model;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugElement;
import org.key_project.sed.core.model.impl.AbstractSEDDebugElement;

/**
 * A SED debug element represents an artifact in a program being
 * symbolically debugged.
 * <p>
 * Some methods on debug elements require communication
 * with the target program. Such methods may throw a {@link DebugException}
 * with a status code of {@link DebugException#TARGET_REQUEST_FAILED}
 * when unable to complete a request due to a failure on the target.
 * Methods that require communication with the target program or require
 * the target to be in a specific state (for example, suspended), are declared
 * as such.
 * </p>
 * <p>
 * Debug elements are language independent. However, language specific
 * features can be made available via the adapter mechanism provided by
 * {@link IAdaptable}, or by extending the debug element interfaces.
 * A debug model is responsible for declaring any special adapters 
 * its debug elements implement.
 * </p>
 * <p>
 * A symbolic element is also a normal debug element ({@link IDebugElement})
 * for compatibility reasons with the Eclipse debug API.
 * </p>
 * <p>
 * Clients may implement this interface. It should not be directly instantiated.
 * It is recommended to instantiate always one of the provided sub interfaces
 * and to subclass from {@link AbstractSEDDebugElement}.
 * </p>
 * @author Martin Hentschel
 */
public interface ISEDDebugElement extends IDebugElement {
   /**
    * Returns the debug target this element is contained in.
    * @return the debug target this element is contained in
    */
   public ISEDDebugTarget getDebugTarget();
   
   /**
    * Returns the launch this element is contained in.
    * @return the launch this element is contained in
    */
   public ILaunch getLaunch();
   
   /**
    * Returns a unique ID which identifies this element uniquely in
    * the whole debug model. The ID must be a valid XML name.
    * @return The unique ID of this element which is a valid XML name.
    */
   public String getId();
}